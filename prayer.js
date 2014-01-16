var weekday = new Array(7);
weekday[0] = "Sunday";
weekday[1] = "Monday";
weekday[2] = "Tuesday";
weekday[3] = "Wednesday";
weekday[4] = "Thursday";
weekday[5] = "Friday";
weekday[6] = "Saturday";

Date.prototype.getDayOfWeek = function() {
    return weekday[this.getDay()]; }

Date.prototype.getDayOfYear = function() {
    var onejan = new Date(this.getFullYear(),0,1);
    return Math.ceil((this - onejan) / 86400000); }

var how_many = 5;

$( document ).ready(function() {
    var today = new Date ();
    for ( var i = 0; i < how_many ; i ++ ) {
        var date = new Date ( today.getTime() + (i * 24 * 60 * 60 * 1000) );
        var header = date.getDayOfWeek();
        var day = date.getDayOfYear();
        var schedule = schedules[ day % schedules.length ];

        $('table').find('tr:eq(0)').find('td:last').after('<td>' + header + '</td>');
        for ( var j = 0 ; j < 4 ; j ++ ) {
            $('table').find('tr:eq(' + (1 + j) + ')').find('td:last').after('<td>' + schedule[j] + '</td>'); } } });
