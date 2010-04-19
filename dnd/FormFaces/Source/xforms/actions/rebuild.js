// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new rebuild action.
//
// Parameters:
//     element: The element from which this action was created.
//     model:   The model to rebuild.
function XFormRebuildAction(element, model) {
  assert(model != null, "model is null");
  
  XFormAction.call(this, element);

  this.model = model;
};

XFormRebuildAction.inherits(XFormAction);


XFormParser.prototype.parseRebuildAction = function(element) {
  return new XFormRebuildAction(
    element,
    
    this.parseRebuildActionModel(element)
  );
};

XFormParser.prototype.parseRebuildActionModel = function(element) {
  return xform.getObjectById(element.attributes.getNamedItem("model"));
};


XFormRebuildAction.prototype.activate = function() {
  this.model.rebuild();
  
  this.model.doRebuild     = false;
  this.model.doRecalculate = true;
  this.model.doRevalidate  = true;
  this.model.doRefresh     = true;
  
  xform.rebuilt            = true;
};

XFormRebuildAction.prototype.toString = function() {
  return "rebuild";
};