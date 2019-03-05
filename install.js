
try {
  // Required by a development install, napa is used to obtain the Metamath test suite.
  var napa = require('napa/cli');
} catch(e) {
  // This must be a production install, napa is not present and we don't need it.
};

if(typeof(napa)!=='undefined') {
  napa.cli([]);
}

