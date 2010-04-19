// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


function XFormModel(element, instances, binds, submissions) {
  XFormObject.call(this, element, true);

  this.instances   = instances;
  this.binds       = binds;
  this.submissions = submissions;
  this.controls    = [];

  for (var i = this.instances  .length - 1; i >= 0; --i)  { this.instances  [i].model = this; }
  for (var i = this.submissions.length - 1; i >= 0; --i) { this.submissions[i].model = this; }

  for (var i = this.binds.length - 1; i >= 0; --i) {
    this.binds[i].index = i;
    this.binds[i].setModel(this);
  }
};

XFormModel.inherits(XFormObject);

XFormParser.prototype.parseModels = function(element) {
  for (var child = element.firstChild; child != null; child = child.nextSibling) {
    if (!XForm.isXHtmlElement(child, "head")) {
      continue;
    }
    
    for (var headChild = child.firstChild; headChild != null; headChild = headChild.nextSibling) {
      if (XForm.isXFormsElement(headChild, "model")) {
        xform.models.push(this.parseModel(headChild));
      }
    }
    
    break;
  }

  // XForm.alertTime("Models parsed in %t seconds.");
  this.parseBoundElements(element, null);
  // XForm.alertTime("Bound Elements parsed in %t seconds.");
};


XFormParser.prototype.parseModel = function(element) {
  var instances   = this.parseInstances  (element); // XForm.alertTime("Instances parsed in %t seconds.");
  var binds       = this.parseBinds      (element); // XForm.alertTime("Binds parsed in %t seconds.");
  var submissions = this.parseSubmissions(element); // XForm.alertTime("Submissions parsed in %t seconds.");

  var submissionsLength = submissions.length;
  
  for (var i = 0; i < submissionsLength; ++i) {
    var submission = submissions[i];

    if (submission.bind.type == "ref") {
      binds.push(submission.bind);
    }
  }

  return new XFormModel(element, instances, binds, submissions);
};


XFormModel.prototype.postRender = function() {
  var self = this;
  
  var submissionsLength = this.submissions.length;
  for (var i = 0; i < submissionsLength; ++i) {
    this.htmlNode.appendChild(this.submissions[i].render());
  }
  
  var instancesLength = this.instances.length;
  for (var i = 0; i < instancesLength; ++i) {
    this.htmlNode.appendChild(this.instances[i].render());
  }
  
  this.htmlNode.getInstanceDocument = function(instanceId) {
    return xform.getObjectById(instanceId, XFormInstance).document;
  };
  
  this.htmlNode.rebuild     = function() {                        self.rebuild    (); };
  this.htmlNode.recalculate = function() { self.graph.touchAll(); self.recalculate(); };
  this.htmlNode.revalidate  = function() {                        self.revalidate (); };
  this.htmlNode.refresh     = function() {                        self.refresh    (); };

  // When the page is unloaded, remove these functions to prevent a memory leak in
  // Internet Explorer.
  new EventListener(window, "unload", "default", function() {
    self.htmlNode.getInstanceDocument = null;
    
    self.htmlNode.rebuild     = null;
    self.htmlNode.recalculate = null;
    self.htmlNode.revalidate  = null;
    self.htmlNode.refresh     = null;
  });
};

// Rebuilds the master dependency graph.
XFormModel.prototype.rebuild = function() {
  this.rebuildBindings        (); // XForm.alertTime("Bindings rebuilt in %t seconds.");
  this.rebuildControlInstances(); // XForm.alertTime("Controls instantiated in %t seconds.");
};

XFormModel.prototype.rebuildBindings = function() {
  this.bindings   = [];
  this.graph      = new XFormDependencyGraph(this);
  
  var contextNode = this.instances[0].document.documentElement;
  
  //XForm.startTimer();

  // Create a binding for each bind, and then setup the dependency graph.
  var bindsLength = this.binds.length;
  for (var i = 0; i < bindsLength; ++i) {
    this.binds[i].reset();

    var  binding     = this.binds[i].createBinding(new XPathContext(contextNode, 1, 1));
    this.bindings[i] = binding;

    //XForm.alertTime("Created binding #" + (i+1) + " in %t seconds.\n\n" + binding);
    
    binding.setupGraph(this.graph);
    
    //XForm.alertTime("Setup graph for binding #" + (i+1) + " in %t seconds.\n\n" + binding);
  }
  
  // Set up vertices for each node that inherits "relevant" or "readonly" from an
  // ancestor.
  for (var i in this.graph.vertices) {
    var vertex = this.graph.vertices[i];

    if (vertex.property == "relevant" || vertex.property == "readOnly") {
      addInheritedVertex(vertex, vertex.node);
    }
  }
  

  function addInheritedVertex(vertex, descendantNode) {
    // The first time this function is called, do not add a vertex.
    if (descendantNode != vertex.node) {
      // If the descendant node already has this property, stop.
      if (vertex.graph.getVertex(descendantNode, vertex.property) != null) {
        return;
      }

      // Add a vertex to the descendant node for the inherited property, with a null
      // XPath.
      vertex.graph.addVertex(descendantNode, vertex.property, null, null).dependsOn(vertex);
    }

    var children   = XPathAxis.CHILD    .filterNode(descendantNode);
    var attributes = XPathAxis.ATTRIBUTE.filterNode(descendantNode);
    var childLen   = children  .length;
    var attLen     = attributes.length;

    for (var i = 0; i < childLen; ++i) { addInheritedVertex(vertex, children  [i]); }
    for (var i = 0; i < attLen;   ++i) { addInheritedVertex(vertex, attributes[i]); }
  };
};

XFormModel.prototype.rebuildControlInstances = function() {
  var numControls = this.controls.length;
  
  for (var i = 0; i < numControls; i++) {
    var control  = this.controls[i];
    var htmlNode = xform.getHtmlNode(control.xmlNode);
    
    if (htmlNode == null) {
      var ancestor = control.xmlElement.parentNode;
      
      while (ancestor != null && ancestor.namespaceURI != XmlNamespaces.XFORMS) {
        ancestor = ancestor.parentNode;
      }
      
      switch (ancestor.nodeName.replace(/^.*:/, "")) {
        case "repeat":
        case "switch": 
        case "label" :
          htmlNode = xform.getObjectByNode(ancestor).activeInstance.container;
          break;
          
        default:
          htmlNode = document.createElement("span");
          break;
      }
    }
    
    while (htmlNode.hasChildNodes()) {
      htmlNode.removeChild(htmlNode.lastChild);
    }
    
    control.instance = control.instantiate(null, null, 0, htmlNode);
    
    if (control.enclosedBy != null) {
      var numInnerControls = control.enclosedBy.innerControls.length;
      
      for (var j = 0; j < numInnerControls; ++j) {
        if (control.enclosedBy.innerControls[j] == control) {
          control.enclosedBy.instance.innerControlInstances[0][j] = control.instance;
          break;
        }
      }
    }
    
    control.instance.activate();
  }
};

// Recalculates all of the model item properties.
XFormModel.prototype.recalculate = function() {
  var updated = "";

  // Get a sub-graph containing only the changed vertices.
  var subGraph            = this.graph.getPertinentSubGraph();
  var independentVertices = [];
  
  for (var i in subGraph.vertices) {
    var vertex = subGraph.vertices[i];
    
    if (vertex.inDegree == 0) {
      independentVertices.push(vertex);
    }
  }
  
  // Each iteration, find an independent vertex, recalculate its value, and then
  // decrement the inDegree of its dependents. An independent vertex is one whose
  // value doesn't depend on any other vertex in the sub-graph (i.e. inDegree is
  // 0).
  var subVertexLen = subGraph.count;
  for (var j = 0; j < subVertexLen; ++j) {
    if (independentVertices.length == 0) {
      throw new XFormComputeException("Dependency graph contains a cycle.");
    }
    
    var subVertex = independentVertices.pop();
    var vertex    = this.graph.vertices[subVertex.index];
    
    // Decrease the inDegree of all of the subgraph vertex's dependents and add them
    // to the independent vertex list if their inDegree goes to 0.
    var dependents   = subVertex.dependents;
    var dependentLen = dependents.length;
    for (var i = 0; i < dependentLen; ++i) {
      var dependent = dependents[i];
      
      if (--dependent.inDegree == 0) {
        independentVertices.push(dependent);
      }
    }
    
    if (updated != "") {
      updated += ", ";
    }

    updated += vertex;

    switch (vertex.property) {
      case "text":
        updated += " = \"" + vertex.getValue() + "\"";

        // Mark the vertex as changed.
        vertex.touch();
        break;

      // Calculate vertices are a special case; they change the value of the "text"
      // vertex for their nodes, rather than setting their own value.
      case "calculate":
        var value = XPath.STRING_FUNCTION.evaluate(vertex.xpath.evaluate(vertex.context));

        updated += " := \"" + value + "\"";

        this.graph.getVertex(vertex.node, "text").setValue(value);
        break;

      // Inheritable properties.
      case "relevant":
      case "readOnly":
        switch (vertex.property) {
          case "relevant": var defaultValue = true;  break;
          case "readOnly": var defaultValue = false; break;
        }

        var parentNode   = XPathAxis.PARENT.filterNode(vertex.node)[0];
        var parentVertex = (parentNode == null) ? null : this.graph.getVertex(parentNode, vertex.property);

        if (parentVertex != null && parentVertex.value != defaultValue) {
          var value = parentVertex.getValue();
        }
        else if (vertex.xpath != null) {
          var value = XPath.BOOLEAN_FUNCTION.evaluate(vertex.xpath.evaluate(vertex.context));
        }
        else {
          var value = defaultValue;
        }

        updated += " := " + value;

        vertex.setValue(value);
        
        break;

      // Non-inheritable properties.
      case "required":
      case "constraint":
        var value      = XPath.BOOLEAN_FUNCTION.evaluate(vertex.xpath.evaluate(vertex.context));
        var textVertex = this.graph.getVertex(vertex.node, "text");

        updated += " := " + value;

        vertex.setValue(value);
        
        //needs to have the "(vertex.value && !textVertex.isValid)" check so that it will update the isValid
        //boolean from when it was invalid otherwise it would stay invalid.
        if(!vertex.value || (vertex.value && !textVertex.isValid)) {
          textVertex.isValid = value;
          for (var ancestor = vertex.node.parentNode; ancestor != null; ancestor = ancestor.parentNode) {
            textVertex = this.graph.getVertex(ancestor, "text");
            
            if (textVertex != null) {
              textVertex.isValid = value;
            }
          }
        }
        
        break;

      default:
        throw new XmlException("Unknown property: " + vertex.property);
    }
  }

  status("Calculated: " + updated);
};

XFormModel.prototype.revalidate = function() {
  var refreshed = "";
  
  // For each changed vertex, notify its bindings of the new value.
  var changedVertices  = this.graph.changedVertices;
  var changedVertexLen = changedVertices.length;
  for (var i = 0; i < changedVertexLen; ++i) {
    var vertex = changedVertices[i];

    vertex.refresh();

    var controls   = vertex.controls;
    var controlLen = controls.length;
    for (var j = 0; j < controlLen; ++j) {
      if (refreshed != "") {
        refreshed += ", ";
      }

      refreshed += controls[j];
    }
  }
  
  // Notify each waiting listener that a property value has changed. This loop
  // must be written this way rather than as "for (var i in xform...)"
  // because listeners can be added to the list while iterating over the array,
  // and the for...in syntax doesn't process those new listeners.
  for (var i = 0; i < xform.waitingListeners.length; ++i) {
    var listener = xform.waitingListeners[i][0];
    var control  = xform.waitingListeners[i][1];
    var property = xform.waitingListeners[i][2];
    var value    = xform.waitingListeners[i][3];
    
    if (control.binding == null || this.haveChanged(control.binding.boundNodes, property)) {
      listener(control, property, value);
    }
  }

  xform.waitingListeners = [];

  this.graph.resetChangedVertices();
  
  status("Revalidated: " + refreshed);
};

// Refresh the values of each control based on the values of the instance nodes.
// Doesn't do anything code has been moved up into the revalidate function.
XFormModel.prototype.refresh = function() {
  status("");
};

// Returns true if any model item properties have changed; otherwise, false.
XFormModel.prototype.hasChanged = function() {
  return this.graph.changedVertices.length > 0;
};

// Returns true if the specified property has changed for any of the nodes in
// the specified node-set.
//
// Parameters:
//     nodeSet:  A set of nodes to check.
//     property: The property to check. If not specified, defaults to "text".
//
// Return value:
//     the value of the node if any of the nodes' properties have changed, null if not.
XFormModel.prototype.haveChanged = function(nodeSet, property) {
  if (typeof(property) == "undefined") {
    property = "text";
  }

  var setLen = nodeSet.length;
  for (var i = 0; i < setLen; ++i) {
    var vertex = this.graph.getVertex(nodeSet[i], property);

    if (vertex != null && vertex.hasChanged) {
      return true;
    }
  }

  return false;
};


function clearStatus() {
  var statusElement = document.getElementById("status");

  if (statusElement != null) {
    while (statusElement.hasChildNodes()) {
      statusElement.removeChild(statusElement.lastChild);
    }
  }
};

function status(message) {
  var statusElement = document.getElementById("status");

  if (statusElement != null) {
    statusElement.appendChild(document.createTextNode(message));
    statusElement.appendChild(document.createElement ("br"));
  }
};


XmlEvent.define("xforms-rebuild",     "Events", true, true, function(event) { xform.getObjectForHtmlNode(event.target).rebuild    (); });
XmlEvent.define("xforms-recalculate", "Events", true, true, function(event) { xform.getObjectForHtmlNode(event.target).recalculate(); });
XmlEvent.define("xforms-revalidate",  "Events", true, true, function(event) { xform.getObjectForHtmlNode(event.target).revalidate (); });
XmlEvent.define("xforms-refresh",     "Events", true, true, function(event) { xform.getObjectForHtmlNode(event.target).refresh    (); });
XmlEvent.define("xforms-reset",       "Events", true, true, function(event) { xform.getObjectForHtmlNode(event.target).reset      (); });