// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Interface for all XPath expressions, which evaluate to either a string,
// number, boolean, or node-set.
function XPathExpression() {
};

// Evaluate the expression.
XPathExpression.prototype.evaluate = function(context) {
  assert(false, "evaluate not implemented");
};

// Returns a list of the nodes referenced by this expression.
XPathExpression.prototype.referencedNodes = function(context) {
  var value = this.evaluate(context);
  
  if (instanceOf(value, NodeSet)) {
    return value;
  }
  else {
    return new NodeSet();
  }
};



// Creates a new literal expression, which always returns the specified (string)
// literal.
function XPathLiteralExpression(literal) {
  this.literal = literal.toString();
};

XPathLiteralExpression.inherits(XPathExpression);

XPathLiteralExpression.prototype.evaluate = function(context) {
  return this.literal;
};



// Creates a new number expression, which always returns the specified number.
function XPathNumberExpression(number) {
  this.number = Number(number);
};

XPathNumberExpression.inherits(XPathExpression);

XPathNumberExpression.prototype.evaluate = function(context) {
  return this.number;
};



// Creates a new filter expression, which evaluates an expression and filters
// the resultant node-set with a predicate.
function XPathFilterExpression(expression, predicate) {
  this.expression = expression;
  this.predicate  = predicate;
};

XPathFilterExpression.inherits(XPathExpression);

XPathFilterExpression.prototype.evaluate = function(context) {
  return this.predicate.filter(context, this.expression.evaluate(context), XPathAxis.Direction.FORWARD);
};



// Creates a new path expression, which returns the result of evaluating the
// specified location path.
function XPathPathExpression(filterExpression, locationPath) {
  this.filterExpression = filterExpression;
  this.locationPath     = locationPath;
};

XPathPathExpression.inherits(XPathExpression);

XPathPathExpression.prototype.evaluate = function(context) {
  return this.locationPath.filter(context, this.filterExpression.evaluate(context));
};



// Creates a new function call expression, which calls the specified function
// and yields its return value.
//
// Parameters:
//     functionQName: The name of the function to evaluate.
//     arguments:     An array of expressions which are evaluated and used as
//                    arguments to the function.
function XPathFunctionCallExpression(functionQName, arguments) {
  this.functionQName = functionQName;
  this.arguments     = arguments;
};

XPathFunctionCallExpression.inherits(XPathExpression);

XPathFunctionCallExpression.prototype.evaluate = function(context) {
  var func      = context.lookupFunction(this.functionQName);
  var arguments = [];
  
  if (func == null) {
    throw new XmlException("XPath function \"" + this.functionQName + "\" not found.");
  }

  var argLen = this.arguments.length;
  for (var i = 0; i < argLen; ++i) {
    arguments.push(this.arguments[i].evaluate(context));
  }
  
  return func.call(context, arguments);
};

XPathFunctionCallExpression.prototype.referencedNodes = function(context) {
  if (this.arguments.length == 0) {
    var func = context.lookupFunction(this.functionQName);
    
    if (func == null) {
      throw new XmlException("XPath function \"" + this.functionQName + "\" not found.");
    }
    
    if (func.defaultTo != null) {
      return new NodeSet([context.node]);
    }
    else {
      return new NodeSet();
    }
  }
  else {
    var referencedNodes = new NodeSet();
  
    for (var i = this.arguments.length - 1; i >= 0; --i) {
      referencedNodes.addAll(this.arguments[i].referencedNodes(context));
    }
    
    return referencedNodes;
  }
};


// Creates a new unary expression.
//
// Parameters:
//     operator: The unary operator, which must be "-".
//     operand:  The operand.
function XPathUnaryExpression(operator, operand) {
  if (arguments.length == 0) {
    return;
  }
  
  this.operator = operator;
  this.operand  = operand;
};

XPathUnaryExpression.inherits(XPathExpression);

XPathUnaryExpression.prototype.evaluate = function(context) {
  switch (this.operator) {
    case "-":
      return -XPath.NUMBER_FUNCTION.evaluate(this.operand.evaluate(context));
    
    default:
      assert(false, "Invalid unary operator: " + this.operator);
  }
};


// Creates a new binary expression, which evaluates arithmetic and relational
// expressions.
//
// Parameters:
//     operator:     The binary operator, as a string like "+" or "and".
//     leftOperand:  The sub-expression to the left of the operator.
//     rightOperand: The sub-expression to the right of the operator.
function XPathBinaryExpression(operator, leftOperand, rightOperand) {
  if (arguments.length == 0) {
    return;
  }
  
  this.operator     = this.operators[operator];
  this.leftOperand  = leftOperand;
  this.rightOperand = rightOperand;
  
  assert(this.operator, "Invalid operator: " + operator);
};

XPathBinaryExpression.inherits(XPathExpression);

XPathBinaryExpression.prototype.evaluate = function(context) {
  return this.operator.evaluate(
    this.leftOperand .evaluate(context),
    this.rightOperand.evaluate(context)
  );                            
};

XPathBinaryExpression.prototype.referencedNodes = function(context) {
  return this.leftOperand .referencedNodes(context).addAll(
         this.rightOperand.referencedNodes(context));
};


XPathBinaryExpression.Operator = function() {
};

XPathBinaryExpression.Operator.prototype.evaluate = function(left, right) {
};


XPathBinaryExpression.UnionOperator = function() {
};

XPathBinaryExpression.UnionOperator.prototype.evaluate = function(left, right) {
  return new NodeSet(left).addAll(right);
};


XPathBinaryExpression.BooleanOperator = function(handler) {
  this.handler = handler;
};

XPathBinaryExpression.BooleanOperator.prototype.evaluate = function(left, right) {
  left  = XPath.BOOLEAN_FUNCTION.evaluate(left);
  right = XPath.BOOLEAN_FUNCTION.evaluate(right);
  
  return this.handler(left, right);
};


XPathBinaryExpression.ComparisonOperator = function(handler) {
  this.handler = handler;
};

// See section 3.4 of the XPath specification for an explanation of this function.
XPathBinaryExpression.ComparisonOperator.prototype.evaluate = function(left, right) {
  // If both objects to be compared are node-sets...
  if (instanceOf(left, NodeSet) && instanceOf(right, NodeSet)) {
    for (var i = left.length - 1; i >= 0; --i) {
      for (var j = right.length - 1; j >= 0; --j) {
        if (this.compare(XPathFunction.stringValueOf(left[i]), XPathFunction.stringValueOf(right[j]))) {
          return true;
        }
      }
    }
    
    return false;
  }

  // If one object to be compared is a node-set and the other is a
  // [number / string / boolean]...
  if (instanceOf(left, NodeSet)) {
    switch (right.constructor) {
      case Number:
        for (var i = left.length - 1; i >= 0; --i) {
          if (this.compare(XPath.NUMBER_FUNCTION.evaluate(XPathFunction.stringValueOf(left[i])), right)) {
            return true;
          }
        }
        
        return false;
        
      case String:
        for (var i = left.length - 1; i >= 0; --i) {
          if (this.compare(XPathFunction.stringValueOf(left[i]), right)) {
            return true;
          }
        }
        
        return false;
        
      case Boolean:
        return this.compare(XPath.BOOLEAN_FUNCTION.evaluate(left), right);
    }
  }
  
  if (instanceOf(right, NodeSet)) {
    switch (left.constructor) {
      case Number:
        for (var i = right.length - 1; i >= 0; --i) {
          if (this.compare(left, XPath.NUMBER_FUNCTION.evaluate(XPathFunction.stringValueOf(right[i])))) {
            return true;
          }
        }
        
        return false;
        
      case String:
        for (var i = right.length - 1; i >= 0; --i) {
          if (this.compare(left, XPathFunction.stringValueOf(right[i]))) {
            return true;
          }
        }
        
        return false;
        
      case Boolean:
        return this.compare(left, XPath.BOOLEAN_FUNCTION.evaluate(right));
    }
  }
  
  return this.compare(left, right);
};


XPathBinaryExpression.EqualityOperator = function(handler) {
  this.handler = handler;
};

XPathBinaryExpression.EqualityOperator.inherits(XPathBinaryExpression.ComparisonOperator);

XPathBinaryExpression.EqualityOperator.prototype.compare = function(left, right) {
  if (instanceOf(left, Boolean) || instanceOf(right, Boolean)) {
    left  = XPath.BOOLEAN_FUNCTION.evaluate(left);
    right = XPath.BOOLEAN_FUNCTION.evaluate(right);
  }
  else if (instanceOf(left, Number) || instanceOf(right, Number)) {
    left  = XPath.NUMBER_FUNCTION.evaluate(left);
    right = XPath.NUMBER_FUNCTION.evaluate(right);
  }
  else {
    // Both left and right are strings.
  }
  
  return this.handler(left, right);
};


XPathBinaryExpression.RelationalOperator = function(handler) {
  this.handler = handler;
};

XPathBinaryExpression.RelationalOperator.inherits(XPathBinaryExpression.ComparisonOperator);

XPathBinaryExpression.RelationalOperator.prototype.compare = function(left, right) {
  left  = XPath.NUMBER_FUNCTION.evaluate(left);
  right = XPath.NUMBER_FUNCTION.evaluate(right);
  
  return this.handler(left, right);
};


XPathBinaryExpression.ArithmeticOperator = function(handler) {
  this.handler = handler;
};

XPathBinaryExpression.ArithmeticOperator.prototype.evaluate = function(left, right) {
  left  = XPath.NUMBER_FUNCTION.evaluate(left);
  right = XPath.NUMBER_FUNCTION.evaluate(right);

  return this.handler(left, right);  
};

XPathBinaryExpression.prototype.operators = {
  "|":   new XPathBinaryExpression.UnionOperator     (),
  
  "or":  new XPathBinaryExpression.BooleanOperator   (function(left, right) { return left || right; }),
  "and": new XPathBinaryExpression.BooleanOperator   (function(left, right) { return left && right; }),
  "=":   new XPathBinaryExpression.EqualityOperator  (function(left, right) { return left == right; }),
  "!=":  new XPathBinaryExpression.EqualityOperator  (function(left, right) { return left != right; }),
  "<=":  new XPathBinaryExpression.RelationalOperator(function(left, right) { return left <= right; }),
  "<":   new XPathBinaryExpression.RelationalOperator(function(left, right) { return left <  right; }),
  ">=":  new XPathBinaryExpression.RelationalOperator(function(left, right) { return left >= right; }),
  ">":   new XPathBinaryExpression.RelationalOperator(function(left, right) { return left >  right; }),

  "+":   new XPathBinaryExpression.ArithmeticOperator(function(left, right) { return left +  right; }),
  "-":   new XPathBinaryExpression.ArithmeticOperator(function(left, right) { return left -  right; }),
  "*":   new XPathBinaryExpression.ArithmeticOperator(function(left, right) { return left *  right; }),
  "div": new XPathBinaryExpression.ArithmeticOperator(function(left, right) { return left /  right; }),
  "mod": new XPathBinaryExpression.ArithmeticOperator(function(left, right) { return left %  right; })
};