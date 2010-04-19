// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new refresh action.
//
// Parameters:
//     element: The element from which this action was created.
//     model:   The model to refresh.
function XFormRefreshAction(element, model) {
  assert(model != null, "model is null");
  
  XFormAction.call(this, element);

  this.model = model;
};

XFormRefreshAction.inherits(XFormAction);


XFormParser.prototype.parseRefreshAction = function(element) {
  return new XFormRefreshAction(
    element,
    
    this.parseRefreshActionModel(element)
  );
};

XFormParser.prototype.parseRefreshActionModel = function(element) {
  return xform.getObjectById(element.attributes.getNamedItem("model"));
};


XFormRefreshAction.prototype.activate = function() {
  this.model.refresh();
  this.model.doRefresh = false;
};

XFormRefreshAction.prototype.toString = function() {
   return "refresh";
};