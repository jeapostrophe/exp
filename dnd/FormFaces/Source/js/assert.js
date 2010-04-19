// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function assert(condition, message) {
  if (!condition) {
    throw new AssertionException(message);
  }
};


function AssertionException(message) {
  this.message   = message;
  this.callstack = stackTrace();
};

AssertionException.prototype.toString = function() {
  var message = (this.message ? "Assertion failed: " + this.message : "Assertion failed.");
  
  if (this.callstack != "") {
    message += "\n\nStack trace:\n" + this.callstack;
  }
  
  return message;
};