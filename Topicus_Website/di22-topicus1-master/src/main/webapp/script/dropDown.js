//JQuery for drop down and changing style of form

$(document).ready(function() {
    $('#font').change(function() {
        let font = $(this).val();
        $('#registration-form').css('font-family', font);
    });

    $('#color').change(function() {
        let color = $(this).val();
        $('#registration-form').css('background-color', color);
    });
});


//Regular javascript no jquery
// document.getElementById('font').addEventListener('change', function() {
//     var font = this.value;
//     var form = document.getElementById('registration-form');
//     form.style.fontFamily = font;
// });
//
// document.getElementById('color').addEventListener('change', function() {
//     var color = this.value;
//     var form = document.getElementById('registration-form');
//     form.style.backgroundColor = color;
// });
