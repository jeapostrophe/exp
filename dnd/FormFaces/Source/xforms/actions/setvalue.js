// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new setvalue action.
//
// Parameters:
//     element: The element from which this action was created.
//     bind:    The action's bind.
//     value:   The XPath expression or string literal value.
function XFormSetValueAction(element, bind, value) {
  assert(bind  != null, "setvalue: bind is null");
  assert(value != null, "setvalue: value is null");
  
  XFormAction.call(this, element);

  this.bind  = bind;
  this.value = value;
};

XFormSetValueAction.inherits(XFormAction);


XFormParser.prototype.parseSetValueAction = function(element) {
  return new XFormSetValueAction(
    element,
    
    this.getBindFor              (element),
    this.parseSetValueActionValue(element)
  );
};

XFormParser.prototype.parseSetValueActionValue = function(element) {
  var value = this.xpathValue(element, "value", null);
  
  if (value == null) {
    value = XPathFunction.stringValueOf(element);
  }
  
  return value;
};


XFormSetValueAction.prototype.activate = function() {
  var boundNodes = this.bind.defaultBinding.getBoundNodes();
  
  // If the <setvalue/> action is bound to an empty node-set, return immediately.
  if (boundNodes.length == 0) {
    return;
  }
  
  var node   = boundNodes[0];
  var vertex = this.bind.model.graph.addVertex(node, "text");
  var value  = this.value;
  
  if (instanceOf(value, XPath)) {
    value = XPath.STRING_FUNCTION.evaluate(value.evaluate(new XPathContext(node, 1, boundNodes.length)));
  }
  
  vertex.setValue(value);
  
  this.bind.model.doRecalculate = true;
  this.bind.model.doRevalidate  = true;
  this.bind.model.doRefresh     = true;
};

XFormSetValueAction.prototype.toString = function() {
  return xmlSerialize(this.xmlNode);
};