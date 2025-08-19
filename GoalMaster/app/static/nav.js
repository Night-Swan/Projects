function updateNavbar() {
    const token = localStorage.getItem('access_token');
    const navLinks = document.getElementById('nav-links');
    if (!navLinks) return;

    // Get the current page URL path
    const currentPath = window.location.pathname;

    if (token) {
        navLinks.innerHTML = `
            <a href="/" class="nav-link${currentPath === '/' ? ' active' : ''}">Home</a>
            <a href="/tasks.html" class="nav-link${currentPath === '/tasks.html' ? ' active' : ''}">Tasks</a>
            <a href="/user/profile.html" class="nav-link${currentPath === '/user/profile.html' ? ' active' : ''}">Profile</a>
            <button class="logout-button" onclick="logout()">Logout</button>
        `;
    } else {
        navLinks.innerHTML = `
            <a href="/" class="nav-link${currentPath === '/' ? ' active' : ''}">Home</a>
            <a href="/register" class="nav-link${currentPath === '/register' ? ' active' : ''}">Register</a>
            <a href="/login" class="nav-link${currentPath === '/login' ? ' active' : ''}">Login</a>
        `;
    }
}

function logout() {
    localStorage.removeItem('access_token');
    window.location.href = '/';
}

document.addEventListener('DOMContentLoaded', updateNavbar);