
const sqlRejectWords =  ["SELECT", "FROM", "ALTER", "TABLE", "DROP", "TRUNCATE", "UNION", "INSERT", "UPDATE", "DELETE", "JOIN", "WHERE", "EXEC", "CREATE", "GRANT", "REVOKE", "COMMIT", "ROLLBACK"].map(x => x.toLowerCase());

const xssRejectWords = ["script", "<", ">", "javascript", "img", "src", "--", "//", "/*", "!"];

/**
 * Check for faulty values like undefined, null, '', 0 ... Etc.
 * @param {string} input - the user input
 * @returns {true} on non-empty user input
 */
export function isEmpty(input) {
    if (input) return false;
    else return true;
}

function sanitize(input) {
    const pattern = /[\@\+\_\-\.\/\=\s]/g;
    while(pattern.test(input)) {
        input = input.replace(pattern, "");
    }
    return input;
}

export function inputSanitizer(input) {
    const lower = sanitize(input.toString().toLowerCase());
    let valid = true;
    let sqlCount = 0;
    if (containsAlphanumeric(lower)) {
        sqlRejectWords.forEach(word => {
            if (lower.includes(word)) {
                sqlCount++;
            }
        });
        xssRejectWords.forEach(word => {
            if (lower.includes(word)) {
                valid = false;
            }
        });
        if (sqlCount >= 2) {
            valid = false;
        }
        return valid;
    }
    return false;
    //alert("The input: '" + input + "' contains questionable character sequence. Please remove any non-alphanumeric characters, or invalid terms.");
}

export function validEmail(email) {
    const emailRegex = /^(\w+\.?)+@(\w{2,}\.?)+$/g;
    return emailRegex.test(email);
}

/**
 * Method used for presentation of user input, to prevent script execution.
 * @param text
 * @returns {*}
 */
function manageDisplay(text) {
    return text.replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/'/g, '&#x27;')
        .replace(/`/g, '&#x60;')
        .replace(/"/g, '&quot;')
        .replace(/&/g, '&amp;');
}

/**
 * Basic method to test whether an input contains ONLY alphanumeric values. Uses String Regex to accomplish this task.
 * Allows commas and period signs.
 * @param input of type String, representing user input.
 * @returns {boolean}
 */
function containsAlphanumeric(input) {
    const alNum = /^[a-zA-Z0-9.,]+$/;
    return alNum.test(input);
}

/**
 * Encoding to UTF-8 to be used to ensure attackers cannot use different encoding mechanisms to pass malicious actions.
 * @param input
 * @returns {string}
 */
function encodeUTF8(input) {
    const e = new TextEncoder();
    const eInput = e.encode(input);
    const d = new TextDecoder();
    return d.decode(eInput);
}