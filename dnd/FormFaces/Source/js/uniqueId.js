// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function uniqueId() {
  return "ff-" + ++uniqueId.counter;
};

uniqueId.counter = 0;
        
        
function executeSequentially() {
  var functions = [];
  
  function execute() {
    if (functions.length == 0) {
      return;
    }
    
    functions.shift()();
    setTimeout(functionCall(monitor, execute), 1);
  };
  
  var args = arguments.length;
  for (var i = 0; i < args; ++i) {
    functions.push(arguments[i]);
  }
  
  monitor(execute);
};