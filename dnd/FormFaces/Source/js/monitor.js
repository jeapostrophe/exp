// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function monitor(code) {
  try {    
    code();
  }
  catch (exception) {
    var message   = exception.toString();
    var callstack = stackTrace(exception);
    
    if (message == "[object Error]") {
      message = "";

      for (var i = 0; i < exception.length; ++i) {
        message += i + ": " + exception[i] + "\n";
      }
    }
    
    message = "An error has occurred!\n\n" + message;
    
    if (callstack != "") {
      if (!message.match(/\n$/)) {
        message += "\n";
      }
      
      message += "\nStack trace:\n" + callstack;
    }
    
    alert(message);

//    throw exception;
  }
};