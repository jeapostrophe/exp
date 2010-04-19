// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Exception thrown when an error is encountered while loading the XForms
// document.
//
// Parameters:
//     badNode: The invalid node in the XML document.
//     message: An error message.
//     cause:   The exception that caused this exception to be thrown.                                                      
function XFormException(badNode, message, cause) {
  this.badNode = badNode;
  this.message = message;
  this.cause   = cause;
};

XFormException.prototype.toString = function() {
  var message = this.message;
  
  if (this.cause) {
    message += "\n" + this.cause;
  }
  
  return message;
};