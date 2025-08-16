function updateNavbar() {
    const token = localStorage.getItem('access_token');
    const navLinks = document.getElementById('nav-links');
    if (!navLinks) return;

    if (token) {
        navLinks.innerHTML = `
            <a href="/" class="nav-link">Home</a>
            <a href="/tasks.html" class="nav-link">Tasks</a>
            <a href="/user/profile.html" class="nav-link">Profile</a>
            <button class="logout-button" onclick="logout()">Logout</button>
        `;
    } else {
        navLinks.innerHTML = `
            <a href="/" class="nav-link">Home</a>
            <a href="/register" class="nav-link">Register</a>
            <a href="/login" class="nav-link">Login</a>
        `;
    }
}

function logout() {
    localStorage.removeItem('access_token');
    window.location.href = '/';
}

document.addEventListener('DOMContentLoaded', updateNavbar);