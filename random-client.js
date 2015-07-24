var net = require('net');
var async = require('async');
var count = parseInt(process.argv[2]);

function randomInt (low, high) {
    return Math.floor(Math.random() * (high - low) + low);
}

var q = async.queue(function ( data, allDone ) {
    var newRandom = data.random;
    var i = data.iteration;
    var tryAgain = function () {
	var client = new net.Socket();
	client.connect(9123, "127.0.0.1", function () {
	    client.on('data', function (data) {
		var lines = data.toString().split("\n");
		//	    console.log("Bah humbug", lines);
		lines.map(function (data) {
		    if ( data == 'TxCommitted' ) {
//			console.timeEnd('insert');
			client.destroy();
			allDone();
		    } else if (data == 'TxCannotMerge') {
			console.log("Could not merge ", newRandom, "... trying again");
			client.destroy();
			tryAgain();
		    } else if (data != '()' && data.toString().substring(0, 5) != "Moved"&& data != "" ) {
			console.log("Client reported error: " + data);
			client.destroy();
			process.exit();
		    }
		});
	    });

	    client.write("down 0\n");
	    console.log("[" + i + "] insert", newRandom);
//	    console.time('insert');
	    client.write("insert " + newRandom + " \"This is key " + newRandom + "\"\n");
//	    client.write("commit\n");
	});
    }
    tryAgain();
},  2);

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
