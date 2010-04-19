// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function stackTrace(exception) {
  // Internet Explorer
  if (userAgent.isInternetExplorer) {
    var callstack = [];
    
    for (var caller = arguments.caller; caller != null; caller = caller.caller) {
      var name       = caller.name ? caller.name : "<anonymous>";
      var parameters = [];
      var len = caller.length;
      
      for (var i = 0; i < len; ++i) {
        parameters.push("?");
      }
      
      callstack.push(name + "(" + parameters.join(", ") + ")");
    }
  }
  // Mozilla
  else if (userAgent.isMozilla) {
    if (!exception || !exception.stack) {
      try {
        var x; x.y;
      }
      catch (e) {
        exception = e;
      }
    }
    
    if (!exception.stack) {
      return "(stack trace not available)\n";
    }
    
    var callstack  = exception.stack.split("\n");
    var commonPath = null;
    
    // callstack.shift(); // Get rid of the call to stackTrace().
    callstack.pop  (); // Remove the last entry, an empty string.
    
    // Break up the lines into method/file/line components, and figure out the
    // common directory all of the source files are in so that it can be removed
    // from the file names (to make the alert message easier to read).
    for (var i = 0; i < callstack.length; ++i) {
      /^(.*?)@(.*?):(\d+)$/.test(callstack[i]);
      
      var method = RegExp.$1;
      var file   = RegExp.$2;
      var line   = RegExp.$3;
      var path   = file.replace(/^(.*\/).*$/, "$1");
      
      callstack[i] = {method: method, file: file, line: line};
      
      if (file != "") {
        if (commonPath == null) {
          commonPath = path;
        }
        else {
          commonPath = commonPath.substr(0, path      .length);
          path       = path      .substr(0, commonPath.length);
          
          while (commonPath != path) {
            commonPath = commonPath.substr(0, commonPath.length - 1);
            path       = path      .substr(0, path      .length - 1);
          }
        }
      }
    }
    
    // Create a string for each function call.
    for (var i = 0; i < callstack.length; ++i) {
      var method = callstack[i].method;
      var file   = callstack[i].file;
      var line   = callstack[i].line;
      
      if (file == "" && method == "") {
        continue;
      }
      
      var call = "";
      
      if (file == "") {
        call += "<unknown>";
      }
      else {
        call += file.substr(commonPath.length) + "(" + line + ")";
      }
      
      if (method != "") {
        call += ": ";
        
        if (method.match(/^\(/)) {
          call += "<anonymous>";
        }
        
        call += method;
      }
        
      callstack[i] = call;
    }
  }
  else {
    var callstack = [];
  }
  
  var string = "";
  
  for (var i = 0; i < callstack.length; ++i) {
    string += "> " + callstack[i] + "\n";
  }

  
  return string;
};