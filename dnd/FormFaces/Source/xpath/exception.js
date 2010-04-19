// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function XPathException(xpath, position, cause) {
  this.xpath    = xpath;
  this.position = position;
  this.cause    = cause;
};

XPathException.prototype.toString = function() {
  var message = "Syntax error at character " + (this.position + 1) + " '"
              + this.xpath.substr(this.position, 1) + "': " + this.xpath;
              
  if (this.cause != null) {
    message += "\nCause: " + this.cause;
  }
  
  return message;
};


// Exception thrown when the namespace URI for an XML namespace prefix cannot be
// resolved.
//
// Parameters:
//     contextNode: The node from which the prefix was to be resolved.
//     prefix:      The prefix that could not be resolved.
function XPathInvalidPrefixException(contextNode, prefix) {
  this.contextNode = contextNode;
  this.prefix      = prefix;
};

XPathInvalidPrefixException.inherits(XPathException);

XPathInvalidPrefixException.prototype.toString = function() {
  return 'Unable to resolve namespace prefix "' + this.prefix + '".';
};


// Exception thrown when there is an invalid character in an XPath string.
//
// Parameters:
//     xpath:    The invalid XPath string.
//     position: The position of the invalid character.
function XPathInvalidCharacterException(xpath, position) {
  XPathException.call(this, xpath, position);
};

XPathInvalidCharacterException.inherits(XPathException);


// Thrown when an invalid token is encountered during parsing.
//
// Parameters:
//     token: The invalid token.
function XPathInvalidTokenException(token) {
  XPathException.call(this, token.xpath, token.position);
  this.token = token;
};

XPathInvalidTokenException.inherits(XPathException);