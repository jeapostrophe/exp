// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Generic interface for all XPath functions. Functions take any number of
// parameters and return either a string, number, boolean, or node.
//
// To call the function, you can either use call() or call evaluate() directly
// with the parameters to the function.
//
// Parameters:
//    body:          The body of the function.
//    acceptContext: If true, then the context is passed as the first parameter
//                   to the function. When declaring your own functions, it is
//                   recommended that you use XPathFunction.NO_CONTEXT or
//                   XPathFunction.REQUIRE_CONTEXT.
//    defaultTo:     Optional. If given, specifies what the default argument to
//                   the function should be if no arguments are given. Can be
//                   either XPathFunction.DefaultTo.CONTEXT_NODE or
//                   XPathFunction.DefaultTo.CONTEXT_STRING, in which case the
//                   default argument is the value of the string() function
//                   applied to the context node.
function XPathFunction(body, acceptContext, defaultTo) {
  this.evaluate      = body;
  this.acceptContext = acceptContext;
  this.defaultTo     = defaultTo;
};

XPathFunction.Context                   = { };
XPathFunction.Context.NONE              = false;
XPathFunction.Context.REQUIRED          = true;

XPathFunction.DefaultTo                 = { };
XPathFunction.DefaultTo.NOTHING         = null;
XPathFunction.DefaultTo.CONTEXT_NODE    = 0;
XPathFunction.DefaultTo.CONTEXT_NODESET = 1;
XPathFunction.DefaultTo.CONTEXT_STRING  = 2;

// Call the function. You can call evaluate() directly if you know the signature
// of the function being called.
//
// Parameters:
//     context:   The function call context.
//     arguments: An array containing the arguments to the function, if any.
//
// Return value:
//     The return value of the function.
XPathFunction.prototype.call = function(context, arguments) {
  // If there were no arguments given, see if the function accepts a default argument.
  if (arguments.length == 0) {
    switch (this.defaultTo) {
      case XPathFunction.DefaultTo.CONTEXT_NODE:
        if (context.node != null) {
          arguments = [context.node];
        }
        
        break;
        
      case XPathFunction.DefaultTo.CONTEXT_NODESET:
        if (context.node != null) {
          arguments = [new NodeSet([context.node])];
        }
        
        break;

      case XPathFunction.DefaultTo.CONTEXT_STRING:
        arguments = [XPath.STRING_FUNCTION.evaluate(new NodeSet([context.node]))];
        break;

      default:
        break;
    }
  }
  
  if (this.acceptContext) {
    arguments.unshift(context);
  }

  return this.evaluate.apply(null, arguments);
};
 
 
XPathFunction.stringValueOf = function(node) {
  switch (node.nodeType) {
    case 1:   // Element
    case 9:   // Document
    case 11:  // Document fragment
      var string = "";

      for (var child = node.firstChild; child != null; child = child.nextSibling) {
        switch (child.nodeType) {
          case 1: // Element
          case 3: // Text
          case 4: // CDATA section
            string += XPathFunction.stringValueOf(child);
            break;
            
          default:
            break;
        }
      }

      return string;

    case 2:   // Attribute
    case 3:   // Text
    case 4:   // CDATA section
    case 8:   // Comment
    case 7:   // Processing instruction
      return node.nodeValue;

    case 5:   // Entity reference
    case 6:   // Entity
    case 10:  // Document type
    case 12:  // Notation
      throw new XmlException("Unexpected node type: " + node.nodeType + " [" + node.nodeName + "]");
  }
};