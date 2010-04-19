// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new XPath expression parser, which constructs parse trees from
// XPath strings.
function XPathParser() {
  this.cache = { };
};

// Parses an XPath expression string.
// 
// Parameters:
//     xpath:       An XPath expression string.
//     contextNode: An XML node from which to lookup the namespace URIs for the
//                  namespace prefixes in the XPath expression.
// 
// Return value:
//     The parse tree for the XPath.
// 
// Exceptions:
//     XPathException: Thrown if an error occurred while parsing the XPath
//     expression.
XPathParser.prototype.parse = function(xpath, contextNode) {
  // If this XPath has been seen before, return the cached XPathExpression.
  var cache;
  
  if (cache = this.cache[xpath]) {
    for (var i = cache.length - 1; i >= 0; --i) {
      if (cache[i][0] == contextNode) {
        return cache[i][1];
      }
    }
  }
  
  this.tokenizer    = new XPathTokenizer(xpath);
  this.contextNode  = contextNode;
  this.currentToken = this.tokenizer.currentToken;
  
  var expression    = this.parseExpression();
  
  this.needToken(XPathTokenType.END);
  
  // Save the expression in the cache.
  if (typeof(this.cache[xpath]) == "undefined") {
    this.cache[xpath] = [];
  }
  
  this.cache[xpath].push([contextNode, expression]);
  
  // Return.
  return expression;
};

XPathParser.prototype.parseExpression = function() {
  return this.parseOrExpression();
};

XPathParser.prototype.parseOrExpression             = function() { return this.parseBinaryExpression(this.parseAndExpression,            "left", [XPathTokenType.OR]); };
XPathParser.prototype.parseAndExpression            = function() { return this.parseBinaryExpression(this.parseEqualityExpression,       "left", [XPathTokenType.AND]); };
XPathParser.prototype.parseEqualityExpression       = function() { return this.parseBinaryExpression(this.parseRelationalExpression,     "left", [XPathTokenType.EQUALS, XPathTokenType.NOT_EQUALS]); };
XPathParser.prototype.parseRelationalExpression     = function() { return this.parseBinaryExpression(this.parseAdditiveExpression,       "left", [XPathTokenType.LESS_THAN, XPathTokenType.GREATER_THAN, XPathTokenType.LESS_THAN_OR_EQUAL_TO, XPathTokenType.GREATER_THAN_OR_EQUAL_TO]); };
XPathParser.prototype.parseAdditiveExpression       = function() { return this.parseBinaryExpression(this.parseMultiplicativeExpression, "left", [XPathTokenType.PLUS, XPathTokenType.MINUS]); };
XPathParser.prototype.parseMultiplicativeExpression = function() { return this.parseBinaryExpression(this.parseUnaryExpression,          "left", [XPathTokenType.MULTIPLY, XPathTokenType.DIV, XPathTokenType.MOD]); };
XPathParser.prototype.parseUnionExpression          = function() { return this.parseBinaryExpression(this.parsePathExpression,           "left", [XPathTokenType.UNION]); };

// Parses a binary expression, which is composed of two sub-expressions
// separated by an operator.
// 
// Parameters:
//     parseSubExpression: The function to parse a sub-expression.
//     associativity:      The associativity of this expression.
//     operators:          A list of valid operators.
// 
// Return value:
//     A new expression.
XPathParser.prototype.parseBinaryExpression = function(parseSubExpression, associativity, operators) {
  // Returns true if array contains item; otherwise, false.
  function contains(array, item) {
    var arrayLen = array.length;
    for (var i = 0; i < arrayLen; ++i) {
      if (array[i] == item) {
        return true;
      }
    }
    
    return false;
  };
  
  switch (associativity) {
    case "left": {
      var expression = parseSubExpression.call(this);
      
      while (contains(operators, this.currentToken.type)) {
        var operator = this.currentToken;

        this.nextToken();
        
        expression = new XPathBinaryExpression(operator.lexeme, expression, parseSubExpression.call(this));
      }
      
      return expression;
    }

    case "right": {
      var expression = parseSubExpression.call(this);

      if (contains(operators, this.currentToken.type)) {
        var operator = this.currentToken;

        this.nextToken();

        expression = new XPathBinaryExpression(
          operator.lexeme,
          expression,
          parseBinaryExpression(parseSubExpression, associativity, operators)
        );
      }

      return expression;
    }
  }
};

XPathParser.prototype.parseUnaryExpression = function() {
  if (this.currentToken.type != XPathTokenType.MINUS) {
    return this.parseUnionExpression();
  }

  var operator = this.currentToken;

  this.nextToken();

  return new XPathUnaryExpression(operator.lexeme, this.parseUnaryExpression());
};

XPathParser.prototype.parsePathExpression = function() {
  var filterExpression = this.parseFilterExpression();
  var locationPath     = null;
  
  if (filterExpression == null || this.currentToken.type == XPathTokenType.SLASH || this.currentToken.type == XPathTokenType.SLASH_SLASH) {
    locationPath = this.parseLocationPath();
  }
  
  if (locationPath == null) {
    return filterExpression;
  }
  else if (filterExpression == null) {
    return locationPath;
  }
  else {
    locationPath.isAbsolute = false;

    return new XPathPathExpression(filterExpression, locationPath);
  }
};

// Will return null instead of throwing an exception if unable to parse a filter
// expression.
XPathParser.prototype.parseFilterExpression = function() {
  var expression = this.parsePrimaryExpression();

  if (expression == null) {
    return null;
  }

  while (this.currentToken.type == XPathTokenType.LEFT_BRACKET) {
    expression = new XPathFilterExpression(expression, this.parsePredicate());
  }

  return expression;
};

// Will return null instead of throwing an exception if unable to parse a
// primary expression.
XPathParser.prototype.parsePrimaryExpression = function() {
  var expression = null;

  switch (this.currentToken.type) {
    case XPathTokenType.VARIABLE_REFERENCE:
      expression = new XPathVariableReferenceExpression(new QName(this.currentToken.lexeme.substr(1), this.contextNode));

      this.nextToken();
      break;

    case XPathTokenType.LEFT_PARENTHESIS:
      this.skipToken(XPathTokenType.LEFT_PARENTHESIS);

      expression = this.parseExpression();

      this.skipToken(XPathTokenType.RIGHT_PARENTHESIS);
      break;

    case XPathTokenType.LITERAL:
      expression = new XPathLiteralExpression(this.currentToken.lexeme.slice(1, -1));

      this.nextToken();
      break;

    case XPathTokenType.NUMBER:
      expression = new XPathNumberExpression(new Number(this.currentToken.lexeme));

      this.nextToken();
      break;

    case XPathTokenType.FUNCTION_NAME:
      expression = this.parseFunctionCall();
      break;
  }

  return expression;
};

XPathParser.prototype.parseFunctionCall = function() {
  this.needToken(XPathTokenType.FUNCTION_NAME);

  var functionName = new QName(this.currentToken.lexeme, this.contextNode);
  var arguments    = [];

  this.nextToken();
  this.skipToken(XPathTokenType.LEFT_PARENTHESIS);

  if (this.currentToken.type != XPathTokenType.RIGHT_PARENTHESIS) {
    arguments.push(this.parseExpression());

    while (this.currentToken.type == XPathTokenType.COMMA) {
      this.nextToken();
      arguments.push(this.parseExpression());
    }
  }

  this.skipToken(XPathTokenType.RIGHT_PARENTHESIS);

  return new XPathFunctionCallExpression(functionName, arguments);
};

XPathParser.prototype.parsePredicate = function() {
  this.skipToken(XPathTokenType.LEFT_BRACKET);

  var expression = this.parseExpression();

  this.skipToken(XPathTokenType.RIGHT_BRACKET);

  return new XPathPredicate(expression);
};

XPathParser.prototype.parseLocationPath = function() {
  var isAbsolute;
  var stepsRequired;
  var steps = [];

  switch (this.currentToken.type) {
    case XPathTokenType.SLASH:
      isAbsolute    = true;
      stepsRequired = 0;

      this.nextToken();
      break;

    case XPathTokenType.SLASH_SLASH:
      isAbsolute    = true;
      stepsRequired = 2;

      steps.push(new XPathStep(XPathAxis.DESCENDANT_OR_SELF, new XPathNodeNodeTest(), []));

      this.nextToken();
      break;

    default:
      isAbsolute    = false;
      stepsRequired = 1;

      break;
  }
  
  steps = steps.concat(this.parseRelativeLocationPath());
  
  if (steps.length < stepsRequired) {
    throw new XPathInvalidTokenException(this.currentToken);
  }

  return new XPathLocationPath(isAbsolute, steps);
};

// Returns the list of steps in the path, which will be empty if unable to parse
// a relative location path.
XPathParser.prototype.parseRelativeLocationPath = function() {
  var steps = [];

  // Each iteration parses one step of the path. The loop terminates when no more
  // steps are found.
  while (true) {
    switch (this.currentToken.type) {
      case XPathTokenType.DOT:
        steps.push(new XPathStep(XPathAxis.SELF, new XPathNodeNodeTest(), []));

        this.nextToken();
        break;

      case XPathTokenType.DOT_DOT:
        steps.push(new XPathStep(XPathAxis.PARENT, new XPathNodeNodeTest(), []));

        this.nextToken();
        break;

      default:
        // Axis
        var axis        = XPathAxis.CHILD;
        var defaultAxis = true;

        if (this.currentToken.type.isAxisName) {
          switch (this.currentToken.type) {             
            case XPathTokenType.ANCESTOR:           axis = XPathAxis.ANCESTOR;           break;
            case XPathTokenType.ANCESTOR_OR_SELF:   axis = XPathAxis.ANCESTOR_OR_SELF;   break;
            case XPathTokenType.ATTRIBUTE:          axis = XPathAxis.ATTRIBUTE;          break;
            case XPathTokenType.CHILD:              axis = XPathAxis.CHILD;              break;
            case XPathTokenType.DESCENDANT:         axis = XPathAxis.DESCENDANT;         break;
            case XPathTokenType.DESCENDANT_OR_SELF: axis = XPathAxis.DESCENDANT_OR_SELF; break;
            case XPathTokenType.FOLLOWING:          axis = XPathAxis.FOLLOWING;          break;
            case XPathTokenType.FOLLOWING_SIBLING:  axis = XPathAxis.FOLLOWING_SIBLING;  break;
            case XPathTokenType.NAMESPACE:          axis = XPathAxis.NAMESPACE;          break;
            case XPathTokenType.PARENT:             axis = XPathAxis.PARENT;             break;
            case XPathTokenType.PRECEDING:          axis = XPathAxis.PRECEDING;          break;
            case XPathTokenType.PRECEDING_SIBLING:  axis = XPathAxis.PRECEDING_SIBLING;  break;
            case XPathTokenType.SELF:               axis = XPathAxis.SELF;               break;
          }

          defaultAxis = false;

          this.nextToken();
          this.skipToken(XPathTokenType.COLON_COLON);
        }
        else if (this.currentToken.type == XPathTokenType.ATTRIBUTE_SIGN) {
          axis        = XPathAxis.ATTRIBUTE;
          defaultAxis = false;

          this.nextToken();
        }
        
        // Node test
        var nodeTest;

        try {
          switch (this.currentToken.type) {
            case XPathTokenType.STAR:
              nodeTest = new XPathStarNodeTest();

              this.nextToken();
              break;

            case XPathTokenType.NAMESPACE_TEST:
              nodeTest = new XPathNamespaceNodeTest(QName.lookupNamespaceURI(this.contextNode, this.currentToken.lexeme.split(":")[0]));

              this.nextToken();
              break;

            case XPathTokenType.QNAME:
              nodeTest = new XPathQNameNodeTest(new QName(this.currentToken.lexeme, this.contextNode));

              this.nextToken();
              break;

            case XPathTokenType.COMMENT:
              nodeTest = new XPathCommentNodeTest();

              this.nextToken();
              this.skipToken(XPathTokenType.LEFT_PARENTHESIS);
              this.skipToken(XPathTokenType.RIGHT_PARENTHESIS);
              break;

            case XPathTokenType.TEXT:
              nodeTest = new XPathTextNodeTest();

              this.nextToken();
              this.skipToken(XPathTokenType.LEFT_PARENTHESIS);
              this.skipToken(XPathTokenType.RIGHT_PARENTHESIS);
              break;

            case XPathTokenType.PROCESSING_INSTRUCTION:
              this.nextToken();
              this.skipToken(XPathTokenType.LEFT_PARENTHESIS);

              if (this.currentToken.type == XPathTokenType.LITERAL) {
                nodeTest = new XPathProcessingInstructionNodeTest(this.currentToken.lexeme.slice(1, -1));

                this.nextToken();
              }
              else {
                nodeTest = new XPathProcessingInstructionNodeTest();
              }

              this.skipToken(XPathTokenType.RIGHT_PARENTHESIS);
              break;

            case XPathTokenType.NODE:
              nodeTest = new XPathNodeNodeTest();
              
              this.nextToken();
              this.skipToken(XPathTokenType.LEFT_PARENTHESIS);
              this.skipToken(XPathTokenType.RIGHT_PARENTHESIS);
              break;

            default:
              if (defaultAxis && steps.length == 0) {
                return [];
              }

              // Either an invalid node test, or a missing step.
              throw new XPathInvalidTokenException(this.currentToken);
          }
        }
        // Bad namespace prefix.
        catch (exception) {
          throw new XPathException(this.currentToken.xpath, this.currentToken.position, exception);
        }

        // Predicates
        var predicates = [];

        while (this.currentToken.type == XPathTokenType.LEFT_BRACKET) {
          predicates.push(this.parsePredicate());
        }

        steps.push(new XPathStep(axis, nodeTest, predicates));
        break;
    }
    
    // Look for a '/' or '//' token; if we see one, we go back to the top of the
    // loop to find the next step.
    switch (this.currentToken.type) {
      case XPathTokenType.SLASH:
        this.nextToken();
        break;

      case XPathTokenType.SLASH_SLASH:
        steps.push(new XPathStep(XPathAxis.DESCENDANT_OR_SELF, new XPathNodeNodeTest(), []));

        this.nextToken();
        break;

      default:
        return steps;
    }
  }
};


// Gets the next token from the tokenizer.
XPathParser.prototype.nextToken = function() {
  this.tokenizer.next();
  this.currentToken = this.tokenizer.currentToken;
};

// Verifies that the current token's type is one of the specified types. If not,
// throws an exception.
// 
// Parameters:
//     expectedTokenType: The type of token that is expected.
// 
// Exceptions:
//     XPathInvalidTokenException: Thrown if the current token isn't in the
//     list.
XPathParser.prototype.needToken = function(expectedTokenType) {
  if (this.currentToken.type != expectedTokenType) {
    throw new XPathInvalidTokenException(this.currentToken);
  }
};

// Skips over the current token, provided that its type is one of the specified
// types.
// 
// Parameters:
//     expectedTokenType: The type of token that is expected.
// 
// Exceptions:
//     XPathInvalidTokenException: Thrown if the current token is not in the
//     list of tokens to skip.
XPathParser.prototype.skipToken = function(expectedTokenType) {
  this.needToken.call(this, expectedTokenType);
  this.nextToken();
};