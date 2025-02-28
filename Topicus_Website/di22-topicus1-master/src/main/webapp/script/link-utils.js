export function copyLink(link_element_id) {
    var linkElement = document.getElementById(link_element_id);

    var tempInput = document.createElement('input');
    tempInput.style.display = 'none';
    tempInput.value = linkElement.innerText;

    document.body.appendChild(tempInput);

    tempInput.select();
    tempInput.setSelectionRange(0, 99999); // For mobile devices

    navigator.clipboard.writeText(tempInput.value).then(function () {
        document.body.removeChild(tempInput);

        alert('Link text copied!');
    }).catch(function (error) {
        console.error('Failed to copy link text:', error);
    });
}