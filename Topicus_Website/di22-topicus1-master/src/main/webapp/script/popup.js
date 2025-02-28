const styles = `
<style>
#popup {
    position: fixed;
    inset: 0;
    background: #0000005e;
    display: none;
    justify-content: center;
    align-items: center;
}
#popup.visible {
    display: flex;
}
#popup div {
    width: 100%;
    max-width: 800px;
    background: white;
    border-radius: 8px;
    padding: 32px;
}
</style>
`

export function renderPopup(content) {
    const popup = document.createElement('div');
    popup.id = "popup";
    popup.innerHTML = `<div>${content}</div>`
    document.body.append(styles)
    document.body.append(popup)
}

export function showPopup() {
    document.getElementById('popup').className += " visible"
}

export function hidePopup() {

}