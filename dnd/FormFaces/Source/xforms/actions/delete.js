// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new delete action.
//
// Parameters:
//     element: The element from which this action was created.
//     bind:    The action's bind.
//     at:      An XPath expression evaluated to determine location of the
//              element to delete.
function XFormDeleteAction(element, bind, at) {
  assert(bind != null, "delete: bind is null");
  assert(at   != null, "delete: at is null");
 
  XFormAction.call(this, element);

  this.bind = bind;
  this.at   = at;
};

XFormDeleteAction.inherits(XFormAction);


XFormParser.prototype.parseDeleteAction = function(element) {
  return new XFormDeleteAction(
    element,
    
    this.getBindFor         (element),
    this.parseDeleteActionAt(element)
  );
};

XFormParser.prototype.parseDeleteActionAt = function(element) {
  return this.xpathValue(element, "at");
};


XFormDeleteAction.prototype.activate = function() {
  var nodeSet = this.bind.defaultBinding.getBoundNodes();;
  
  if (nodeSet.length == 0) {
    return;
  }
  
  var at = XPath.ROUND_FUNCTION.evaluate(this.at.evaluate(new XPathContext(nodeSet[0], 1, nodeSet.length)));
  
  if (at < 1 || at > nodeSet.length || isNaN(at)) {
    return;
  }
  
  nodeSet[0].parentNode.removeChild(nodeSet[at - 1]);
  
  // Dispatch an xforms-delete event.
  var instances = this.bind.model.instances.length;
  for (var i = 0; i < instances; i++) {
    var instance = this.bind.model.instances[i];
    
    if (instance.document == nodeSet[0].ownerDocument) {
      XmlEvent.dispatch(instance.htmlNode, "xforms-delete");
      break;
    }
  }
  
  this.bind.model.doRebuild     = true;
  this.bind.model.doRecalculate = true;
  this.bind.model.doRevalidate  = true;
  this.bind.model.doRefresh     = true;
};

XFormDeleteAction.prototype.toString = function() {
  return "delete";
};

// Define the xforms-deleteevent.
XmlEvent.define("xforms-delete", "Events", true, false);