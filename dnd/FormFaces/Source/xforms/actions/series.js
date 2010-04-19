// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new <action/> action, which encapsulates a series of actions.
//
// Parameters:
//     element: The element from which this action was created.
function XFormActionAction(element, actions) {
  assert(actions != null, "actions is null");
  
  XFormAction.call(this, element);
  
  this.actions = actions;
};

XFormActionAction.inherits(XFormAction);


XFormParser.prototype.parseActionAction = function(element) {
  return new XFormActionAction(
    element,
    this.parseActionActionActions(element)
  );
};

XFormParser.prototype.parseActionActionActions = function(element) {
  return this.parseActions(element);
};


XFormActionAction.prototype.activate = function() {
  var acts = this.actions.length;
  for (var i = 0; i < acts; i++) {
    this.actions[i].activate();
  }
};

XFormActionAction.prototype.toString = function() {
  return "action";
};