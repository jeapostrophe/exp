// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function XPathFunctionResolver() {
};

// Returns the function with the specified QName, or null if no such function
// exists.
//
// Parameters:
//     qName: The QName of the function to look up.
//
// Return value:
//     An XPathFunction, or null if there is no such function.
XPathFunctionResolver.prototype.lookupFunction = function(qName) {
};



function XPathFunctionMap() {
  this.functions = { };
};

XPathFunctionMap.inherits(XPathFunctionResolver);

XPathFunctionMap.prototype.lookupFunction = function(qName) {
  return this.functions[qName.toString()];
};

XPathFunctionMap.prototype.registerFunction = function(qName, func) {
  this.functions[qName.toString()] = func;
};

XPathFunctionMap.prototype.toString = function() {
  var string = "";
  
  for (var qName in this.functions) {
    string += qName + ": " + this.functions[qName] + "\n";
  }
  
  return string;
};