import aiohttp
import asyncio
import logging
import ollama
import json
from bs4 import BeautifulSoup
from urllib.parse import quote
from aiohttp import ClientSession, ClientTimeout, TCPConnector
from tenacity import retry, stop_after_attempt, wait_exponential, retry_if_exception_type

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

async def is_valid_snapshot_llm(text: str) -> bool:
    """LLM-based validation for ambiguous snapshots."""
    SYSTEM_PROMPT = """Determine if a webpage snapshot is valid for analysis based on its content. A snapshot is INVALID if it contains:
- Parked domain messages (e.g., domain registration, sponsored listings unrelated to the domain owner, or phrases like 'Sponsored Listings displayed above are served automatically by a third party')
- Error messages (e.g., 'domain suspended,' 'site not found,' 'Verifying your browser,' 'error 404,' 'page not found,' 'seized,' 'law enforcement,' 'server error')
- Blank or nearly empty content (<50 characters of meaningful text)
- Phrases indicating the domain is for sale (e.g., 'this domain is for sale,' 'buy this domain,' or translations like 'osta tämä verkko-osoite' in any language)
- Content stating the site is seized (e.g., 'Operation PowerOFF')
- Default web server landing pages (e.g., Apache2 Debian Default Page)
A snapshot is VALID if it contains operational website content, INCLUDING PROMOTIONAL CONTENT, unless it explicitly indicates domain sales or parking.
Output JSON: {"valid": true | false, "reason": "brief explanation"}."""

    try:
        if not text or len(text.strip()) < 50:
            logger.info("LLM Validation Result: {'valid': False, 'reason': 'Text too short or empty'}")
            return False
        response = ollama.chat(
            model='mistral',
            messages=[
                {'role': 'system', 'content': SYSTEM_PROMPT},
                {'role': 'user', 'content': text[:500]}
            ],
            format='json'
        )
        result = json.loads(response['message']['content'])
        logger.info(f"LLM Validation Result: {result}")
        return result.get('valid', False)
    except Exception as e:
        logger.error(f"LLM Validation Result: {{'valid': False, 'reason': 'Validation error: {str(e)}'}}")
        return False

@retry(
    stop=stop_after_attempt(3),
    wait=wait_exponential(multiplier=1, min=2, max=10),
    retry=retry_if_exception_type((aiohttp.ClientError, asyncio.TimeoutError)),
    before_sleep=lambda retry_state: logger.info(
        f"Retrying fetch_snapshot (attempt {retry_state.attempt_number}) after error: {retry_state.outcome.exception()}"
    )
)
async def fetch_snapshot(session: ClientSession, wayback_url: str, timestamp: str):
    """Fetch and validate a single snapshot with retries, allowing redirects with a delay."""
    try:
        async with session.get(
            wayback_url,
            timeout=ClientTimeout(total=30),
            allow_redirects=True  # Explicitly allow redirects
        ) as response:
            logger.info(f"Snapshot {wayback_url} status: {response.status}")
            # Handle redirects (3xx status codes)
            if 300 <= response.status < 400:
                logger.info(f"Redirect detected for {wayback_url}, waiting 10 seconds before following")
                await asyncio.sleep(10)  # Wait 10 seconds for redirects
                redirect_url = response.headers.get('Location')
                if redirect_url:
                    logger.info(f"Following redirect to {redirect_url}")
                    async with session.get(
                        redirect_url,
                        timeout=ClientTimeout(total=30)
                    ) as redirect_response:
                        logger.info(f"Redirected snapshot {redirect_url} status: {redirect_response.status}")
                        if redirect_response.status == 200:
                            text = await redirect_response.text()
                            clean_text = extract_text(text)
                            is_valid = await is_valid_snapshot_llm(clean_text)
                            if is_valid:
                                return wayback_url, clean_text, timestamp
            # Handle non-redirect successful responses
            elif response.status == 200:
                text = await response.text()
                clean_text = extract_text(text)
                is_valid = await is_valid_snapshot_llm(clean_text)
                if is_valid:
                    return wayback_url, clean_text, timestamp
            return None, None, None
    except Exception as e:
        logger.error(f"Snapshot {wayback_url} fetch failed: {str(e)}")
        raise

async def process_snapshot(semaphore: asyncio.Semaphore, session: ClientSession, snapshot: list):
    """Process a single snapshot with semaphore for concurrency control."""
    async with semaphore:
        timestamp = snapshot[1]
        wayback_url = f"http://web.archive.org/web/{timestamp}/{snapshot[2]}"
        logger.info(f"Checking snapshot: {wayback_url}")
        try:
            result = await fetch_snapshot(session, wayback_url, timestamp)
            if result[0] is not None:
                logger.info(f"Valid snapshot found: {wayback_url}")
            else:
                logger.info(f"Snapshot invalid: {wayback_url}")
            return result
        except Exception as e:
            logger.error(f"Snapshot processing failed for {wayback_url}: {str(e)}")
            return None, None, None

async def find_valid_wayback_snapshot(url: str, max_snapshots: int = 10) -> tuple:
    """Fetch a valid Wayback Machine snapshot URL and its content asynchronously, stopping at first valid snapshot."""
    try:
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
        }
        async with ClientSession(
            headers=headers,
            connector=TCPConnector(limit=10),
            timeout=ClientTimeout(total=30)
        ) as session:
            last_timestamp = None
            processed_snapshots = 0

            while True:
                cdx_api_url = f"http://web.archive.org/cdx/search/cdx?url={quote(url)}&output=json&limit={max_snapshots}&filter=statuscode:200&sort=reverse"
                if last_timestamp:
                    cdx_api_url += f"&to={last_timestamp}"

                try:
                    logger.info(f"Fetching snapshots from CDX API: {cdx_api_url}")
                    async with session.get(cdx_api_url) as response:
                        if response.status != 200:
                            logger.warning(f"CDX API request failed with status {response.status}")
                            await asyncio.sleep(2)
                            continue

                        data = await response.json()
                        if not data or len(data) <= 1:
                            logger.info("No more snapshots available")
                            return None, None, None

                        snapshots = data[1:]
                        if not snapshots:
                            logger.info("No more snapshots available")
                            return None, None, None

                        logger.info(f"Checking {len(snapshots)} snapshots (processed total: {processed_snapshots})")
                        semaphore = asyncio.Semaphore(10)
                        tasks = [process_snapshot(semaphore, session, snapshot) for snapshot in snapshots]
                        results = await asyncio.gather(*tasks, return_exceptions=True)
                        for result in results:
                            if isinstance(result, tuple) and result[0] is not None:
                                return result[0], result[1], result[2]
                            processed_snapshots += 1

                        last_timestamp = snapshots[-1][1]
                        processed_snapshots += len(snapshots)

                        if len(snapshots) < max_snapshots:
                            logger.info("Reached earliest snapshots")
                            return None, None, None

                        await asyncio.sleep(1)

                except Exception as e:
                    logger.error(f"Error fetching CDX API: {str(e)}")
                    await asyncio.sleep(2)
                    continue

    except Exception as e:
        logger.error(f"Unexpected error in find_valid_wayback_snapshot: {str(e)}")
        return None, None, None

async def scrape_url(url: str) -> str:
    """Scrape the URL directly using aiohttp."""
    try:
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
        }
        async with aiohttp.ClientSession(headers=headers) as session:
            async with session.get(url, timeout=ClientTimeout(total=30), ssl=False) as response:
                response.raise_for_status()
                return await response.text()
    except Exception as e:
        logger.error(f"Error in scrape_url: {str(e)}")
        return None

def extract_text(html: str) -> str:
    """Extract clean text from HTML."""
    try:
        soup = BeautifulSoup(html, 'html.parser')
        for element in soup(['script', 'style', 'nav', 'footer', 'iframe', 'noscript']):
            element.decompose()
        text = soup.get_text(separator=' ', strip=True)
        logger.info(f"The text is {text[:500]}")
        return text[:500] if len(text) > 500 else text
    except Exception:
        return html[:500] if html else ""

def is_captcha_page(text: str) -> bool:
    """Detect if the page is a CAPTCHA or cloud protection page."""
    captcha_keywords = [
        'captcha', 'cloudflare', 'verify you are human', 'checking your browser',
        'cookie error', 'verifying your browser', 'please wait', 'human verification',
        'access denied', 'browser verification'
    ]
    return any(keyword in text.lower() for keyword in captcha_keywords)

async def analyze_url(url: str):
    """Analyze URL to return a valid snapshot, prioritizing live scraping with proper validation."""
    logger.info("Attempting live scraping...")
    live_text = await scrape_url(url)
    
    if live_text:
        clean_live_text = extract_text(live_text)
        
        if is_captcha_page(clean_live_text):
            logger.info("CAPTCHA detected in live scrape, falling back to Wayback Machine...")
            wayback_url, clean_text, timestamp = await find_valid_wayback_snapshot(url)
            if clean_text:
                return {
                    "wayback_url": wayback_url,
                    "content": clean_text,
                    "timestamp": timestamp
                }
            return {
                "wayback_url": None,
                "content": None,
                "timestamp": None,
                "reason": "Live site shows a CAPTCHA verification page, and no valid snapshot found."
            }
        
        if not await is_valid_snapshot_llm(clean_live_text):
            logger.info("Live content failed LLM validation, falling back to Wayback Machine...")
            wayback_url, clean_text, timestamp = await find_valid_wayback_snapshot(url)
            if clean_text:
                return {
                    "wayback_url": wayback_url,
                    "content": clean_text,
                    "timestamp": timestamp
                }
            return {
                "wayback_url": None,
                "content": None,
                "timestamp": None,
                "reason": "Live content failed validation and no valid snapshot found."
            }
        
        return {
            "wayback_url": url,
            "content": clean_live_text,
            "timestamp": None
        }

    logger.info("Live scraping failed, attempting Wayback Machine...")
    wayback_url, clean_text, timestamp = await find_valid_wayback_snapshot(url)
    if clean_text:
        return {
            "wayback_url": wayback_url,
            "content": clean_text,
            "timestamp": timestamp
        }

    logger.info("No valid content found")
    return {
        "wayback_url": None,
        "content": None,
        "timestamp": None,
        "reason": "Failed to scrape URL or find valid snapshot"
    }

if __name__ == "__main__":
    import time
    start_time = time.time()
    URL = "youboot.net"
    result = asyncio.run(analyze_url(URL))
    print(json.dumps(result, indent=2))
    logger.info(f"Runtime: {time.time() - start_time:.2f} seconds")