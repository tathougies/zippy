var net = require('net');
var async = require('async');
var redis = require('redis');
var pool = require('generic-pool');
var count = parseInt(process.argv[2]);

function randomInt (low, high) {
    return Math.floor(Math.random() * (high - low) + low);
}

var sockPool = pool.Pool({
    name: 'redis',
    create: function (cb) {
	var client = redis.createClient();
	cb(null, client);
    },
    destroy: function (obj) {
	client.quit();
    },
    max: 100,
    min: 2,
    // specifies how long a resource can stay idle in pool before being removed
    idleTimeoutMillis : 30000
});

var q = async.queue(function ( data, allDone ) {
    var newRandom = data.random;
    var i = data.iteration;
    var tryAgain = function () {
	sockPool.acquire(function(err, client) {
	    console.log("[" + i + "] insert", newRandom);
	    client.hset("myhash", "" + i, "This is key " + newRandom, function (res) {
		allDone();
		sockPool.release(client);
	    });
	});
    };
    tryAgain();
}, 10);

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
