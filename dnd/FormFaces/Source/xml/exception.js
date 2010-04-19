// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function XmlException(message, cause) {
  this.message = message;
  this.cause   = cause;
};

XmlException.prototype.toString = function() {
  var message = "Error: " + this.message;
  
  if (this.cause != null) {
    message += "\nCause: " + this.cause;
  }
  
  return message;
};