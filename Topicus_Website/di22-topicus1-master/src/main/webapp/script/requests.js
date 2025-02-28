export { get, post, put, del };

/**
 * Generalized method for the HTTP requests.
 * @param {string} url - the path
 * @param {string} method - GET/POST/PUT/DELETE
 * @param {object} data - the data to be sent to the server
 * @returns the first promise after fetching the resource.
 */
async function request(url, method, data) {
    const options = {
        method,
        headers: {}
    };

    if (data !== undefined && data !== null) {
        options.headers['Content-Type'] = 'application/json';
        options.body = JSON.stringify(data);
    } else if (['POST', 'PUT'].includes(method)) {
        throw new Error('Data sent to the server is empty!');
    }

    try {
        const response = await fetch(url, options);
        if (!response.ok && response.status !== 204) {
            const error = await response.json();
            throw new Error(error.message);
        } else if (response.status === 204) {
            return response.text();
        }
        else {
            console.log(response.status);
        }
        return response.json();
        
    } catch (err) {
        alert('Something went wrong!');
        throw err;
    }
}

async function get(url) {
    return request(url, 'get',undefined);
}

async function post(url, data) {
    return request(url, 'post', data);
}

async function put(url, data) {
    return request(url, 'put', data);
}

async function del(url) {
    return request(url, 'delete',undefined);
}