// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates an empty dependency graph.
function XFormDependencyGraph(model) {
  this.model            = model;
  
  this.vertices         = { };
  this.vertexLookupHash = { };
  this.count            = 0;
  
  this.changedVertices  = [];

  this.addVertex(XFormBind.nonRelevantNode, "relevant", new XPathContext(null, null, null), new XPath("false()"));
};

// Adds a "text" vertex to the graph.
//
// Parameters:
//     node:     The vertex node.
//     property: The node property name.
//     xpath:    The property XPath expression, or null if the property is "text".
//
// Return value:
//     The new vertex.
XFormDependencyGraph.prototype.addVertex = function(node, property, context, xpath) {
  assert(node     != null, "node is null");
  assert(property != null, "property is null");
  
  var vertex = this.getVertex(node, property);
  
  if (vertex == null) {
    var hash  = node.nodeName + "." + property;
    var index = this.count++;
    
    vertex               = new XFormDependencyGraphVertex(this, index, node, property, context, xpath);
    this.vertices[index] = vertex;
    
    vertex.touch();

    // Add the vertex to the lookup hash table.
    if (!this.vertexLookupHash[hash]) {
      this.vertexLookupHash[hash] = [];
    }
    
    this.vertexLookupHash[hash].push(vertex);
  }
  else {
    if (property != "text") {
      throw new XmlException("Duplicate model item property: " + property);
    }
  }
  
  return vertex;
};

// Gets a vertex in the graph.
//
// Parameters:
//     node:     The vertex's node.
//     property: The node's property.
//
// Return value:
//     The matching vertex, or null if there is none.
XFormDependencyGraph.prototype.getVertex = function(node, property) {
  var vertices = this.vertexLookupHash[node.nodeName + "." + property];
  
  if (!vertices) {
    return null;
  }
  
  var verticeLen = vertices.length;
  for (var i = 0; i < verticeLen; i++) {
    var vertex = vertices[i];
    
    if (vertex == null) {
      continue;
    }
    
    if (vertex.property != property) {
      continue;
    }
    
    if (vertex.node.isSameNode) {
      if (vertex.node.isSameNode(node)) {
        return vertex;
      }
    }
    else {
      if (vertex.node == node) {
        return vertex;
      }
    }
  }
  
  return null;
};

// Given a list of changed instance data nodes, builds a sub-graph containing
// the vertices for those nodes and those vertices' dependents.
//
// Return value:
//     The sub-graph.
XFormDependencyGraph.prototype.getPertinentSubGraph = function() {
  var subGraph = new XFormDependencyGraph();
  
  subGraph.addSuperGraphVertices(this.changedVertices);
  
  return subGraph;
};

// Taking this graph to be a sub-graph, adds the specified vertices from the
// master graph as well as their dependents. All of the added vertices are
// copies of the vertices from the master graph.
//
// Parameters:
//     vertices: An array of vertices from the master graph.
XFormDependencyGraph.prototype.addSuperGraphVertices = function(vertices) {
  var verticeLen = vertices.length;
  for (var i = 0; i < verticeLen; i++) {
    var vertex = vertices[i];
    
    if (this.vertices[vertex.index] != null) {
      continue;
    }
    
    var parentClone = vertex.clone();
    var dependents  = vertex.dependents;
    
    this.vertices[vertex.index] = parentClone;
    this.count                 += 1;
    
    this.addSuperGraphVertices(dependents);
    
    var dependentLen = dependents.length;
    for (var j = 0; j < dependentLen; ++j) {
      var dependent      = dependents[j];
      var dependentClone = this.vertices[dependent.index];
    
      dependentClone.dependsOn(parentClone);
    }
  }
};

XFormDependencyGraph.prototype.resetChangedVertices = function() {
  var changedVertexLen = this.changedVertices.length;
  for (var i = 0; i < changedVertexLen; ++i) {
    this.changedVertices[i].hasChanged = false;
  }
  
  this.changedVertices = [];
};

XFormDependencyGraph.prototype.touchAll = function() {
  var verticeLen = vertices.length;
  for (var i = 0; i < verticeLen; i++) {
    this.vertices[i].touch();
  }
};

XFormDependencyGraph.prototype.toString = function() {
  var str = "";
  
  var verticeLen = vertices.length;
  for (var i = 0; i < verticeLen; i++) {
    var vertex = this.vertices[i];
    var dependents = vertex.dependents;
    
    str += "#" + i + ": " + vertex + " -- in: " + vertex.inDegree + ", out: [";
    
    var dependentLen = dependents.length;
    for (var j = 0; j < dependentLen; ++j) {
      if (j > 0) {
        str += ", ";
      }
      
      str += dependents[j];
    }
    
    str += "]\n";
  }
  
  return str;
};
  

// Creates a new dependency graph vertex. Only the XFormDependencyGraph object
// should call this constructor; other objects using the graph will call
// graph.addTextVertex and graph.addPropertyVertex.
//
// Parameters:
//     graph:    The graph to which the vertex belongs.
//     index:    The index of the vertex within the containing graph.
//
//     node:     The vertex node.
//     property: The node property.
//     xpath:    The XPath expression for the property. If the property is
//               "text", then this parameter is not needed.
function XFormDependencyGraphVertex(graph, index, node, property, context, xpath) {
  assert(graph != null, "graph is null");
  assert(node  != null, "node is null");
  
  this.graph      = graph;
  this.index      = index;
  
  this.node       = node;
  this.property   = property;
  this.context    = context;
  this.xpath      = xpath;
  this.value      = null;
  
  this.dependents = [];
  this.inDegree   = 0;
  
  this.hasChanged = false;
  this.controls   = [];
  
  if(this.property == "text") {
    this.isValid    = true;
  }
};

// Creates a free-floating copy of this vertex with no dependents and in-degree
// 0.
XFormDependencyGraphVertex.prototype.clone = function() {
  var vertex = new XFormDependencyGraphVertex(
                 this.graph,
                 this.index,
                 this.node,
                 this.property,
                 this.context,
                 this.xpath
               );
  
  vertex.contextNode = this.contextNode;
  vertex.hasChanged  = this.hasChanged;
  
  return vertex;
};

// Adds this vertex to the specified vertex's dependents list.
//
// Parameters:
//     vertex: The vertex that this vertex depends on.
XFormDependencyGraphVertex.prototype.dependsOn = function(vertex) {
  vertex.dependents.push(this);
  ++this.inDegree;
};

XFormDependencyGraphVertex.prototype.setValue = function(value) {
  if (value == this.getValue()) {
    // Commented out this line. Why is it here?
    // Please comment why this is needed if uncommenting...
    // this.graph.changedVertices.push(this);
    
    return;
  }
  
  if (this.property == "text") {
    switch (this.node.nodeType) {
      case 1: // Element
        // Look for the first child text node.
        for (var textNode = this.node.firstChild; textNode != null; textNode = textNode.nextSibling) {
          if (isTextNode(textNode)) {
            break;
          }
        }
        
        if (textNode != null) {
          textNode.nodeValue = value;
        }
        else if (value != "") {
          this.node.insertBefore(this.node.ownerDocument.createTextNode(value), this.node.firstChild);
        }
        
        break;
        
      case 2: // Attribute
      case 3: // Text node
      case 4: // CDATA node
        this.node.nodeValue = value;
        break;
        
      default:
        throw new XFormException(this.node, "Invalid node in dependency graph: " + this.node.nodeName + " (" + this.node.nodeType + ")");
    }
  }
  else {
    this.value = value;
  }
  
  this.touch();
};

// Mark the vertex as changed.
XFormDependencyGraphVertex.prototype.touch = function() {
  if (!this.hasChanged) {
    this.hasChanged = true;
    this.graph.changedVertices.push(this);
  }
};

XFormDependencyGraphVertex.prototype.getValue = function() {
  if (this.property == "text") {
    switch (this.node.nodeType) {
      case 1: // Element
        for (var textNode = this.node.firstChild; textNode != null; textNode = textNode.nextSibling) {
          if (isTextNode(textNode)) {
            return textNode.nodeValue;
          }
        }
        
        return "";
        
      case 2: // Attribute
      case 3: // Text node
      case 4: // CDATA node
        return this.node.nodeValue;
        
      case 9: // Document
        return "";
        
      default:
        throw new XmlException("Unexpected vertex node: " + this.node.nodeName + " (" + this.node.nodeType + ")");
    }
  }
  else {
    return this.value;
  }
};

XFormDependencyGraphVertex.prototype.refresh = function() {
  var value      = this.getValue();
  var property   = this.property;
  var controlLen = this.controls.length;
  
  for (var i = 0; i < controlLen; ++i) {
    this.controls[i].setProperty(property, value);
  }
};

XFormDependencyGraphVertex.prototype.toString = function() {
  var prefix   = (this.node.nodeType == 2) ? "@" : "";
  var name     =  this.node.nodeName;
  var property =  this.property;

  // Code is a huge bottleneck. Commented out for efficiency.
  //
  // if (this.node.nodeType == 1 || this.node.nodeType == 2) {
  //   var size     = new XPath("count(../" + prefix + name + ")")       .evaluate(this.node);
  //   var position = new XPath("count(preceding-sibling::" + name + ")").evaluate(this.node) + 1;
  //   
  //   if (size > 1) {
  //     name += "[" + position + "]";
  //   }
  // }
  
  return prefix + name + "." + property;
};