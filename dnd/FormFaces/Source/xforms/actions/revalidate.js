// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new revalidate action.
//
// Parameters:
//     element: The element from which this action was created.
//     model:   The model to revalidate.
function XFormRevalidateAction(element, model) {
  assert(model != null, "model is null");
  
  XFormAction.call(this, element);

  this.model = model;
};

XFormRevalidateAction.inherits(XFormAction);


XFormParser.prototype.parseRevalidateAction = function(element) {
  return new XFormRevalidateAction(
    element,
    
    this.parseRevalidateActionModel(element)
  );
};

XFormParser.prototype.parseRevalidateActionModel = function(element) {
  return xform.getObjectById(element.attributes.getNamedItem("model"));
};


XFormRevalidateAction.prototype.activate = function() {
  this.model.revalidate();
  
  this.model.doRevalidate = false;
  this.model.doRefresh    = true;
};

XFormRevalidateAction.prototype.toString = function() {
  return "revalidate";
};