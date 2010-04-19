// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function functionCall(method) {
  assert(method != null, "method is null");
  
  var parameters = [];
  var len = arguments.length;
  
  for (var i = 1; i < len; ++i) {
    parameters.push(arguments[i]);
  }
  
  return function() {
    if (method.apply) {
      return method.apply(null, parameters);
    }
    else {
      var jsString = "";
      var paramLen = parameters.length;
      
      for (var i = 0; i < paramLen; i++) {
        if (jsString != "") {
          jsString += ", ";
        }
        
        jsString += "parameters[" + i + "]";
      }
      
      jsString = "method(" + jsString + ")";
      
      return eval(jsString);
    }
  };
};

function methodCall(self, method) {
  assert(self   != null, "self is null");
  assert(method != null, "method is null");
  
  var parameters = [];
  var len = arguments.length;
  
  for (var i = 2; i < len; ++i) {
    parameters.push(arguments[i]);
  }
  
  return function() {
    return self[method].apply(self, parameters);
  };
};