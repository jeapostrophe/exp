// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new recalculate action.
//
// Parameters:
//     element: The element from which this action was created.
//     model:   The model to recalculate.
function XFormRecalculateAction(element, model) {
  assert(model != null, "model is null");
  
  XFormAction.call(this, element);

  this.model = model;
};

XFormRecalculateAction.inherits(XFormAction);


XFormParser.prototype.parseRecalculateAction = function(element) {
  return new XFormRecalculateAction(
    element,
    
    this.parseRecalculateActionModel(element)
  );
};

XFormParser.prototype.parseRecalculateActionModel = function(element) {
  return xform.getObjectById(element.attributes.getNamedItem("model"));
};


XFormRecalculateAction.prototype.activate = function() {
  this.model.recalculate();
  
  this.model.doRecalculate = false;
  this.model.doRevalidate  = true;
  this.model.doRefresh     = true;
};

XFormRecalculateAction.prototype.toString = function() {
  return "recalculate";
};