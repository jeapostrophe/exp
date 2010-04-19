// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new insert action.
//
// Parameters:
//     element:  The element from which this action was created.
//     bind:     The action's bind.
//     at:       An XPath expression evaluated to determine the insert location.
//     position: The position at which to insert the new element, either
//               "before" or "after".
function XFormInsertAction(element, bind, at, position) {
  assert(bind     != null, "insert: bind is null");
  assert(at       != null, "insert: at is null");
  assert(position == "before" || position == "after", "bad position: " + position);
 
  XFormAction.call(this, element);

  this.bind     = bind;
  this.at       = at;
  this.position = position;
};

XFormInsertAction.inherits(XFormAction);


XFormParser.prototype.parseInsertAction = function(element) {
  return new XFormInsertAction(
    element,
    
    this.getBindFor               (element),
    this.parseInsertActionAt      (element),
    this.parseInsertActionPosition(element)
  );
};

XFormParser.prototype.parseInsertActionAt = function(element) {
  return this.xpathValue(element, "at");
};

XFormParser.prototype.parseInsertActionPosition = function(element) {
  return this.stringValue(element, "position");
};


XFormInsertAction.prototype.activate = function() {
  var nodeSet = this.bind.defaultBinding.getBoundNodes();
  
  if (nodeSet.length == 0) {
    return;
  }
  
  var node     = nodeSet[nodeSet.length - 1];
  var clone    = node.cloneNode(true);
  var at       = XPath.ROUND_FUNCTION.evaluate(this.at.evaluate(new XPathContext(nodeSet[0], 1, nodeSet.length)));
  var position = this.position;
  
  if (at < 1)              { at = 1;                                  }
  if (at > nodeSet.length) { at = nodeSet.length;                     }
  if (isNaN(at))           { at = nodeSet.length; position = "after"; }
  
  switch (position) {
    case "before": node.parentNode.insertBefore(clone, nodeSet[at - 1]);             break;
    case "after":  node.parentNode.insertBefore(clone, nodeSet[at - 1].nextSibling); break;
  }
  
  // Dispatch an xforms-insert event.
  var instances = this.bind.model.instances.length;
  for (var i = 0; i < instances; i++) {
    var instance = this.bind.model.instances[i];
    
    if (instance.document == clone.ownerDocument) {
      XmlEvent.dispatch(instance.htmlNode, "xforms-insert");
      break;
    }
  }
  
  this.bind.model.doRebuild     = true;
  this.bind.model.doRecalculate = true;
  this.bind.model.doRevalidate  = true;
  this.bind.model.doRefresh     = true;
};

XFormInsertAction.prototype.toString = function() {
  return "insert";
};

// Define the xforms-insert event.
XmlEvent.define("xforms-insert", "Events", true, false);