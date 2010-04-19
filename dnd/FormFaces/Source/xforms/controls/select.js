// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new select control.
//
// Parameters:
//     element: The element from which the select control was created.
//     bind:    The control's bind.
//     label:   The control's label.
function XFormSelectControl(element, selectMany, bind, innerControls, items, incremental, appearance) {
  assert(bind  != null, "select: bind is null");
  assert(items != null, "select: items is null");
  assert(innerControls != null, "innerControls is null");
  
  var labelControl = null;
  var len = innerControls.length;
  for (var i = 0; i < len; i++) {
    if (innerControls[i] != null && innerControls[i] == "label") {
      labelControl = innerControls[i];
    }
  }
  
  assert(labelControl != null, "select: label is null");
  
  XFormControl.call(this, element, bind, innerControls);
  
  this.selectMany  = selectMany;
  this.items       = items;
  this.incremental = incremental;
  this.appearance  = appearance;
};

XFormSelectControl.inherits(XFormControl);


XFormParser.prototype.parseSelectControl = function(element) {
  return new XFormSelectControl(
    element,
    element.tagName.replace(/^.*:/, "") == "select",
    
    this.getBindFor             (element, true),
    this.parseControls          (element),
    this.parseSelectControlItems(element), 
    this.parseIncremental       (element, true),
    this.parseAppearance        (element, "minimal")
  );
};

XFormParser.prototype.parseSelectControlItems = function(element) {
  var items = [];
  
  for (var childElement = element.firstChild; childElement != null; childElement = childElement.nextSibling) {
    if (childElement.nodeType == 1) {
      var value = null;
      for (var child = childElement.lastChild; child != null; child = child.previousSibling) {
        if (child.nodeType == 1) {
          if (child.nodeName.replace(/^.*:/, "") == "value" && child.namespaceURI == XmlNamespaces.XFORMS) {
            value = child;
            break;
          }
        }
      }
      
      switch (childElement.tagName.replace(/^.*:/, "")) {
        case "item":
          items.push({
            label: this.parseLabel(childElement),
            value: value.firstChild.nodeValue
          });
          
          break;
          
        case "itemset":
          items.push({
            bind:  this.getBindFor(childElement),
            label: this.parseLabel(childElement),
            value: this.getBindFor(value)
          });
          
          break;
      }
    }
  }
  
  return items;
};


XFormSelectControl.prototype.createInstance = function(binding, htmlNode, outerBinding) {
  return new XFormSelectControlInstance(this, binding, htmlNode, outerBinding);
};

function XFormSelectControlInstance(control, binding, htmlNode, outerBinding) {
  assert(binding != null, "binding is null");
  
  var self = this;
      
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding);
  
  this.items = this.getItems();
  var itemLen = this.items.length;
  
  if (this.control.appearance == "full") {
    this.buttons   = [];
    this.groupName = uniqueId();
    this.list      = document.createElement("div");
    
    for (var i = 0; i < itemLen; i++) {
      var listItem = document.createElement("div");
      var type     = control.selectMany ? "checkbox" : "radio";
  
      // Why doesn't "button.name = '...'" work?!
      if (userAgent.isInternetExplorer) {
        var button = document.createElement("<input type='" + type + "' name='" + this.groupName + "' />");
      }
      else {
        var button  = document.createElement("input");
        button.type = type;
      }
      
      button.name = this.groupName;
      button.id   = uniqueId();
      
      listItem .appendChild(button);
      listItem .appendChild(document.createTextNode(" "));
      listItem .appendChild(this.items[i].label.htmlNode);
      this.list.appendChild(listItem);
      
      this.items[i].label.labelElement.setAttribute("for", button.id);
      
      this.valueChangedOn     (button,                           ["click"]);
      this.valueChangedOn     (this.items[i].label.labelElement, ["click"]);
      
      this.watchForFocusChange(button);
      this.activateOnEnter    (button);
            
      this.buttons.push(button);
    }
  }
  else {
    this.selectBox = document.createElement("select");
    
    if (this.control.selectMany) {
      this.selectBox.multiple = true;
    }
    
    if (this.control.selectMany || this.control.appearance == "compact") {
      this.selectBox.size = Math.min(this.items.length, 5);
    }
    
    for (var i = 0; i < itemLen; i++) {
      var option = document.createElement("option");
      var label  = this.items[i].label;
      
      option.appendChild(document.createTextNode(label.getValue()));
      
      (function() {
        var thisOption = option;
        
        // When the label text changes, change the option text.
        label.addListener("text", function(control, property, value) {
          while (thisOption.hasChildNodes()) {
            thisOption.removeChild(thisOption.firstChild);
          }
          
          thisOption.appendChild(document.createTextNode(control.getValue()));
        });
      }) ();
  
      this.selectBox.appendChild(option);
    }
    
    this.selection(this.selectBox, ["keypress", "keydown", "click", "mousedown", "change"]);
    
    this.valueChangedOn(this.selectBox,
      this.control.incremental
        ? ["keypress", "keydown", "click", "mousedown", "change"]
        : ["change"]
    );
    
    this.watchForFocusChange(this.selectBox);
    this.activateOnEnter    (this.selectBox);
  }
};

XFormSelectControlInstance.inherits(XFormControlInstance);

XFormSelectControlInstance.prototype.selection = function(element, eventNames) {
  if (this.binding == null) {
    return;
  }
  
  var events = eventNames.length;
  for (var i = 0; i < events; i++) {
    new EventListener(
      element, eventNames[i], null,
      
      functionCall(setTimeout, methodCall(this, "itemSelected"), 1)
    );
  }
};

XFormSelectControlInstance.prototype.itemSelected = function() {
  XmlEvent.dispatch(this .htmlNode, "xforms-deselect");
  XmlEvent.dispatch(this .htmlNode, "xforms-select");
};

XFormSelectControlInstance.prototype.addInstantiatedLabel = function(label) {
  this.control.label = label;
  
  if (this.control.appearance == "full") {
    this.htmlNode.appendChild(this.addLabel(this.list));
  }
  else {
    this.htmlNode.appendChild(this.addLabel(this.selectBox));
  }
};

XFormSelectControlInstance.prototype.getItems = function() {
  var items = [];
  var itemLen = this.control.items.length;
  
  for (var i = 0; i < itemLen; i++) {
    // <itemset/>
    if (this.control.items[i].bind) {
      var itemset        = this.control.items[i];
      var itemsetBinding = this.binding.innerBindings[0][itemset.bind.index];
      var boundNodesLen  = itemsetBinding.boundNodes.length;
      
      for (var j = 0; j < boundNodesLen; ++j) {
        var valueBinding = itemsetBinding.innerBindings[j][itemset.value.index];
        
        items.push({
          label: itemset.label.instantiate(this, itemsetBinding, j, document.createElement("span")),
          value: XPathFunction.stringValueOf(valueBinding.boundNodes[0])
        });
      }
    }
    // <item/>
    else {
      var item = this.control.items[i];
      
      items.push({
        label: item.label.instantiate(this, this.binding, 0, document.createElement("span")),
        value: item.value
      });
    }
  }
  
  return items;
};

XFormSelectControlInstance.prototype.getValue = function() {
  if (this.control.selectMany && this.control.appearance == "full") {
    var values = [];
    //var blen = this.buttons.length;
    
    for (var i = this.buttons.length - 1; i >= 0; --i) {
      if (this.buttons[i].checked) {
        values.push(this.items[i].value);
      }
    }

    return values.join(" ");
  }
  else if (this.control.selectMany) {
    var values = [];
    //var options = this.selectBox.options.length;
    
    for (var i = this.selectBox.options.length -1; i >= 0; --i) {
      if (this.selectBox.options[i].selected) {
        values.push(this.items[i].value);
      }
    }
    
    return values.join(" ");
  }
  else if (this.control.appearance == "full") {
    //var blen = this.buttons.length;
    for (var i = this.buttons.length - 1; i >= 0; --i) {
      if (this.buttons[i].checked) {
        return this.items[i].value;
      }
    }

    return "";
  }
  else {
    if (this.selectBox.selectedIndex >= 0) {
      return this.items[this.selectBox.selectedIndex].value;
    }

    return "";
  }
};

XFormSelectControlInstance.prototype.setValue = function(value) {
  if (this.control.selectMany && this.control.appearance == "full") {
    // Split the string into individual values, and then select each option whose
    // value is in the list.
    var values = value.split(/\s+/);
    var vals   = values.length;
    
    for (var i = this.items.length - 1; i >= 0; --i) {
      var item   = this.items  [i];
      var button = this.buttons[i];
      
      button.checked = false;
      
      for (var j = vals - 1; j >= 0; --j) {
        if (values[j] == item.value) {
          button.checked = true;
          break;
        }
      }
    }
  }
  else if (this.control.selectMany) {
    // Split the string into individual values, and then select each option whose
    // value is in the list.
    var values = value.split(/\s+/);
    var vals   = values.length;
    
    for (var i = this.items.length - 1; i >= 0; --i) {
      var item   = this.items[i];
      var option = this.selectBox.options[i];
      
      option.selected = false;
      
      for (var j = vals - 1; j >= 0; --j) {
        if (values[j] == item.value) {
          option.selected = true;
          break;
        }
      }
    }
  }
  else if (this.control.appearance == "full") {
    for (var i = this.items.length - 1; i >= 0; --i) {
      if (this.items[i].value == value) {
        this.buttons[i].checked = true;
        return;
      }
    }
  }
  else {
    for (var i = this.items.length - 1; i >= 0; --i) {
      if (this.items[i].value == value) {
        this.selectBox.selectedIndex = i;
        return;
      }
    }
  }
};

XFormSelectControlInstance.prototype.setReadOnly = function(isReadOnly) {
  if (this.control.appearance == "full") {
    var blen = this.buttons.length;
    for (var i = 0; i < blen; i++) {
      this.buttons[i].disabled = isReadOnly;
    }
  }
  else {
    this.selectBox.disabled = isReadOnly;
  }
};


XFormSelectControl        .prototype.toString =
XFormSelectControlInstance.prototype.toString = function() {
  return "select";
};