var net = require('net');
var async = require('async');
var pg = require('pg');
var count = parseInt(process.argv[2]);

var conString = "postgres://tathougies@localhost/postgres";

function randomInt (low, high) {
    return Math.floor(Math.random() * (high - low) + low);
}

var q = async.queue(function ( data, allDone ) {
    var newRandom = data.random;
    var i = data.iteration;
    var tryAgain = function () {
	pg.connect(conString, function (err, client, done) {
//	    console.log("[" + i + "] insert", newRandom);
	    console.time('insert');
	    client.query("insert into simple_tree values ( $1::bigint, $2::text )", ["" + newRandom, "This is key " + newRandom],
			 function (err, result) {
			     if (err) console.log("[" + i + "] Error running query ", err);
			     console.timeEnd('insert');
			     done();
			     allDone();
			 });
	});
    }
    tryAgain();
}, 1);

q.drain = function () {
    console.log("all done");
    process.exit();
}

var queued = {};
async.times(count, function (i, next) {
    var r = randomInt(0, Math.pow(2, 32));
    queued[r]=true;
    q.push({random: r, iteration: i}, function () {
	delete queued[r];
    });
    next(null);
});

setInterval(function () {
    console.log("Queue state", q.running(), queued);
}, 5000);
