// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new dispatch action.
//
// Parameters:
//     element:    The element from which this action was created.
//     name:       The name of the event to dispatch.
//     target:     The ID of the event target element.
//     bubbles:    Boolean indicating if this event bubbles. For predefined
//                 events, this value has no effect.
//     cancelable: Boolean indicating if this event is cancelable. For
//                 predefined events, this value has no effect.
function XFormDispatchAction(element, name, target, bubbles, cancelable) {
  XFormAction.call(this, element);

  this.name       = name;
  this.target     = target;
  this.bubbles    = bubbles;
  this.cancelable = cancelable;
};

XFormDispatchAction.inherits(XFormAction);


XFormParser.prototype.parseDispatchAction = function(element) {
  return new XFormDispatchAction(
    element,

    this.parseDispatchActionName      (element),
    this.parseDispatchActionTarget    (element),
    this.parseDispatchActionBubbles   (element),
    this.parseDispatchActionCancelable(element)
  );
};

XFormParser.prototype.parseDispatchActionName = function(element) {
  return this.stringValue(element, "name");
};

XFormParser.prototype.parseDispatchActionTarget = function(element) {
  return this.stringValue(element, "target");
};

XFormParser.prototype.parseDispatchActionBubbles = function(element) {
  return this.booleanValue(element, "bubbles", "true");
};

XFormParser.prototype.parseDispatchActionCancelable = function(element) {
  return this.booleanValue(element, "cancelable", "true");
};


XFormDispatchAction.prototype.activate = function() {
  var target = new XPath("//*[@id = '" + this.target + "']").selectNode(this.xmlElement);
  var target = xform.getHtmlNode(target);
  
  XmlEvent.dispatch(target, this.name, "Events", this.bubbles, this.cancelable);
};

XFormDispatchAction.prototype.toString = function() {
  return "dispatch";
};