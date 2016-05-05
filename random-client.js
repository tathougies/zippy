var net = require('net');
var async = require('async');
var pool = require('generic-pool');
var count = parseInt(process.argv[2]);

var sockPool = pool.Pool({
    name: 'zippy',
    create: function (cb) {
	var client = new net.Socket();
	client.connect(9123, "127.0.0.1", function () {
	    cb(null, client);
	});
    },
    destroy: function (obj) {
	obj.destroy();
    },
    max: 100,
    min: 2,
    // specifies how long a resource can stay idle in pool before being removed
    idleTimeoutMillis : 30000
});

function randomInt (low, high) {
    return Math.floor(Math.random() * (high - low) + low);
}

var acquireSock = function (cb) {
    sockPool.acquire(function (err, c) {
	if (err) console.log(err);
	else cb(c);
    });
};

var releaseSock = function (c) {
    c.removeAllListeners('data');
    c.write("begin\n");
    sockPool.release(c);
};

var q = async.queue(function ( data, allDone ) {
    var newRandom = data.random;
    var i = data.iteration;
    var tryAgain = function () {
	acquireSock(function (client) {
	    var dataListener = function (data) {
		var lines = data.toString().split("\n");
		//	    console.log("Bah humbug", lines);
		lines.map(function (data) {
		    if ( data == 'TxCommitted' ) {
			//			console.timeEnd('insert');
			releaseSock(client);
			allDone();
		    } else if (data == 'TxCannotMerge') {
			console.log("Could not merge ", newRandom, "... trying again");
			releaseSock(client);
			tryAgain();
		    } else if (data == 'BEGIN' ) {
		    } else if (data != '()' && data.indexOf('ALL DONE') != 0 && data.toString().substring(0, 5) != "Moved"&& data != "" ) {
			console.log("Client reported error: " + data);
			releaseSock(client);
			process.exit();
		    }
		});
	    };
	    client.on('data', dataListener);

	    client.write("down 0\n");
	    console.log("[" + i + "] insert", newRandom);
//	    console.time('insert');
	    client.write("insert " + newRandom + " \"This is key " + newRandom + "\" \n");
	    //	    client.write("query insert-key " + newRandom + " \"This is key " + newRandom + "\" \n");
	    //client.write("txquery insert-key " + newRandom + " \"This is key " + newRandom + "\" \n");
//	    client.write("commit\n");
	});
    }
    tryAgain();
},  10);

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
