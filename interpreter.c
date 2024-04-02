#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "value.h"
#include "linkedlist.h"
#include "talloc.h"
#include "tokenizer.h"
#include "interpreter.h"
#include "parser.h"

// primitivies assignment //
void bind(char *name, Value *(*function)(struct Value *), Frame *frame) { // putting together the symbol with the function into the global frame
    // Add primitive functions to top-level bindings list
    Value *value = talloc(sizeof(Value));
    value->type = PRIMITIVE_TYPE;
    value->pf = function;
    
    Value *symbol = makeNull(); // empty, no info
    symbol -> type = SYMBOL_TYPE; // acts as a string
    symbol -> s = name; // update the value it holds, using the parameter of the func 'name'

    Value *pairing = cons(symbol, value); // link the symbol with the associate function, using value bc it is tied w the func (line 80)
    frame -> bindings = cons(pairing, frame -> bindings); // update the frame with the new paired values
}

Value *primCons(Value *args){
    if (args -> type == NULL_TYPE){
        printf("Evaluation error: cons takes two arguments, three or more supplied.\n");
        texit(0);
    }
    if (args -> c.cdr -> type == NULL_TYPE){
        printf("Evaluation error: cons takes two arguments, three or more supplied.\n");
        texit(0);
    }
    if (args -> c.cdr -> c.cdr -> type != NULL_TYPE){
        printf("Evaluation error: cons takes two arguments, three or more supplied.\n");
        texit(0);
    }
    if (args -> type != CONS_TYPE) {
        printf("Wrong type");
        texit(0);    
    }
    Value *carCon = args -> c.car;
    Value *cdrCon = args -> c.cdr -> c.car;
    if ((cdrCon -> type != NULL_TYPE) && (cdrCon -> type != CONS_TYPE)){
       Value *dotincluded = talloc(sizeof(Value));
       dotincluded -> type = DOT_TYPE;
       return cons(carCon, cons(dotincluded, cons(cdrCon, makeNull())));
    }
    return cons(carCon, cdrCon);
}

Value *primAdd(Value *args){
    Value *result = makeNull();
    Value *cur = args;
    float value = 0;
    double dvalue = 0;
    int doublefound = 0;
    if (args -> type == NULL_TYPE){
        result -> type = INT_TYPE;
        result -> i = 0;
        return result;
    }
    while (cur -> type != NULL_TYPE){
        if ((cur -> c.car -> type != INT_TYPE) && (cur -> c.car -> type != DOUBLE_TYPE)){
            printf("Evaluation error: + must take numbers.\n");
            texit(0);
        }
        if (cur -> c.car -> type == DOUBLE_TYPE){
            doublefound = 1;
            value = cur -> c.car -> d + value;
        }
        else{
            value = cur -> c.car -> i + value;
        }
        cur = cur -> c.cdr;
    }
    if (doublefound == 1){
        result -> type = DOUBLE_TYPE;
        result -> d = value;
    }
    else{
        result -> type = INT_TYPE;
        result -> i = value;
    }
    return result;
}

Value *evalSet(Value *args, Frame *frame){
    if (args -> type == NULL_TYPE){
        printf("Eval error. There should be 2 parameters");
        texit(0);
    }
    if (args -> c.cdr -> type == NULL_TYPE){
        printf("Eval error. There should be 2 parameters");
        texit(0);
    }
    if (args -> c.cdr -> c.cdr -> type != NULL_TYPE){
        printf("Eval error. Too many parameters");
        texit(0);
    }
    Value *voiding = talloc(sizeof(Value));
    voiding -> type = VOID_TYPE; 

    Value *var = args -> c.car; // get the variable or symbol
    Value *expr = eval(args -> c.cdr -> c.car, frame); // get the value associated w the variable
    Value *items = cons(var, expr); // put them together
    frame -> bindings = cons(items, frame->bindings); // update the binding w the new items

    return voiding; 
}

Value *evalLetRec(Value *args, Frame *frame){ 
    Value *middle = args -> c.car;
    Frame *newFrameForLet = talloc(sizeof(Frame));
    newFrameForLet -> bindings = makeNull();
    newFrameForLet -> parent = frame;
    if (middle -> type == NULL_TYPE) {
        return eval(args -> c.cdr -> c.car, newFrameForLet);
    }   
    while (middle -> type != NULL_TYPE) { 
        Value *firstvalofbinding = newFrameForLet -> bindings; // this is after the while loop bc we want to point at the start, since new vals are added in
        while (firstvalofbinding -> type != NULL_TYPE) { 
            if (strcmp(firstvalofbinding -> c.car -> c.car -> s, middle -> c.car -> c.car -> s) == 0) { // a symbol exists in the frame already, cant have duplicates
                printf("This symbol already exists within the frame 117");
                texit(0);
            }
            firstvalofbinding = firstvalofbinding -> c.cdr; // check the next val in the binding
        }
        if (middle -> c.car -> c.car -> type != SYMBOL_TYPE) {
            printf("Error. The first parameter needs to be a symbol 123");
            texit(1);
        }
        else { // we found a symbol type
            if (middle -> c.car -> c.cdr -> type != CONS_TYPE) {
                printf("Error. This is not a cons cell 128");
                texit(1);
            }
            else { // we found a cons type
                Value *resultofeval = eval(middle -> c.car -> c.cdr -> c.car, frame); // value associated with the symbol
                Value *newItems = cons(middle -> c.car -> c.car, resultofeval); // cons together the symbol and the actual value associated with it
                newFrameForLet -> bindings = cons(newItems, newFrameForLet -> bindings); // update the new frame
            }
        }
        middle = middle -> c.cdr;
    }
    args = args->c.cdr;
    return eval(args -> c.car, newFrameForLet);
}

Value *evalBegin(Value *args, Frame *frame){
    Value *result = talloc(sizeof(Value));
    result -> type = VOID_TYPE;

    while (args -> type != NULL_TYPE){
        result = eval(args -> c.car, frame);
        args = args -> c.cdr;
    }
    return result;
}

Value *primSubtract(Value *args){
    Value *result = makeNull();
    Value *cur = args -> c.cdr;
    Value *val_one = args -> c.car;
    float value = 0;
    double dvalue = 0;
    int doublefound = 0;
    if (args -> type == NULL_TYPE){
        result -> type = INT_TYPE;
        result -> i = 0;
        return result;
    }
    while (cur -> type != NULL_TYPE){
        if ((cur -> c.car -> type != INT_TYPE) && (cur -> c.car -> type != DOUBLE_TYPE)){
            printf("Evaluation error: + must take numbers.\n");
            texit(0);
        }
        if (cur -> c.car -> type == DOUBLE_TYPE){
            doublefound = 1;
            value = cur -> c.car -> d + value;
        }
        else{
            value = cur -> c.car -> i + value;
        }
        cur = cur -> c.cdr;
    }
    if (doublefound == 1){
        result -> type = DOUBLE_TYPE;
        result -> d = val_one -> d - value;
    }
    else{
        result -> type = INT_TYPE;
        result -> i = val_one -> i - value;
    }
    return result;
}

Value *primLess(Value *args){
    Value *result = talloc(sizeof(Value));
    result -> s = talloc(sizeof(char)*3);
    result -> type = BOOL_TYPE;
    Value *value1 = args -> c.car;
    Value *value2 = args -> c.cdr -> c.car;
    int resTrue;

    if (args -> type == NULL_TYPE){
        printf("Evaluation error. Not enough parameters");
        texit(0);
    }
    if (args -> c.car -> type == NULL_TYPE){
        printf("Evaluation error. Not enough parameters");
        texit(0);
    }
    if (args -> c.cdr -> type == NULL_TYPE){
        printf("Evaluation error. Not enough parameters");
        texit(0);
    }
    if (args -> c.cdr -> c.cdr -> type != NULL_TYPE){
        printf("Too many parameters");
        texit(0);
    }
    
    if ((value1 -> type == INT_TYPE) && (value2 -> type == INT_TYPE)){
        if ((value1 -> i) < (value2 -> i)){
            resTrue = 1; 
        }
        else{
            resTrue = 0;     
        }
    }
    else if ((value1 -> type == INT_TYPE) && (value2 -> type == DOUBLE_TYPE)){
        if ((value1 -> i) < (value2 -> d)){
            resTrue = 1;
        }
        else{
            resTrue = 0;     
        }
    }
    else if ((value1 -> type == DOUBLE_TYPE) && (value2 -> type == INT_TYPE)){
        if ((value1 -> d) < (value2 -> i)){
            resTrue = 1;
        }
        else{
            resTrue = 0;     
        }
    }
    else if ((value1 -> type == DOUBLE_TYPE) && (value2 -> type == DOUBLE_TYPE)){
        if ((value1 -> d) < (value2 -> d)){
            resTrue = 1;
        }
        else{
            resTrue = 0;     
        }
    }
    if (resTrue == 1){
        result -> s[0] = '#';
        result -> s[1] = 't';
        result -> s[2] = '\0';
    }
    else{
        result -> s[0] = '#';
        result -> s[1] = 'f';
        result -> s[2] = '\0';   
    }
    return result;
}

Value *primEqual(Value *args){
    Value *result = talloc(sizeof(Value));
    result -> s = talloc(sizeof(char)*3);
    result -> type = BOOL_TYPE;
    Value *value1 = args -> c.car;
    Value *value2 = args -> c.cdr -> c.car;
    int resTrue;

    if (args -> type == NULL_TYPE){
        printf("Evaluation error. Not enough parameters");
        texit(0);
    }
    if (args -> c.car -> type == NULL_TYPE){
        printf("Evaluation error. Not enough parameters");
        texit(0);
    }
    if (args -> c.cdr -> type == NULL_TYPE){
        printf("Evaluation error. Not enough parameters");
        texit(0);
    }
    if (args -> c.cdr -> c.cdr -> type != NULL_TYPE){
        printf("Too many parameters");
        texit(0);
    }
    
    if ((value1 -> type == INT_TYPE) && (value2 -> type == INT_TYPE)){
        if ((value1 -> i) == (value2 -> i)){
            resTrue = 1; 
        }
        else{
            resTrue = 0;     
        }
    }
    else if ((value1 -> type == INT_TYPE) && (value2 -> type == DOUBLE_TYPE)){
        if ((value1 -> i) == (value2 -> d)){
            resTrue = 1;
        }
        else{
            resTrue = 0;     
        }
    }
    else if ((value1 -> type == DOUBLE_TYPE) && (value2 -> type == INT_TYPE)){
        if ((value1 -> d) == (value2 -> i)){
            resTrue = 1;
        }
        else{
            resTrue = 0;     
        }
    }
    else if ((value1 -> type == DOUBLE_TYPE) && (value2 -> type == DOUBLE_TYPE)){
        if ((value1 -> d) == (value2 -> d)){
            resTrue = 1;
        }
        else{
            resTrue = 0;     
        }
    }
    if (resTrue == 1){
        result -> s[0] = '#';
        result -> s[1] = 't';
        result -> s[2] = '\0';
    }
    else{
        result -> s[0] = '#';
        result -> s[1] = 'f';
        result -> s[2] = '\0';   
    }
    return result;
}

Value *primGreater(Value *args){
    Value *result = talloc(sizeof(Value));
    result -> s = talloc(sizeof(char)*3);
    result -> type = BOOL_TYPE;
    Value *value1 = args -> c.car;
    Value *value2 = args -> c.cdr -> c.car;
    int resTrue;

    if (args -> type == NULL_TYPE){
        printf("Evaluation error. Not enough parameters");
        texit(0);
    }
    if (args -> c.car -> type == NULL_TYPE){
        printf("Evaluation error. Not enough parameters");
        texit(0);
    }
    if (args -> c.cdr -> type == NULL_TYPE){
        printf("Evaluation error. Not enough parameters");
        texit(0);
    }
    if (args -> c.cdr -> c.cdr -> type != NULL_TYPE){
        printf("Too many parameters");
        texit(0);
    }
    
    if ((value1 -> type == INT_TYPE) && (value2 -> type == INT_TYPE)){
        if ((value1 -> i) > (value2 -> i)){
            resTrue = 1; 
        }
        else{
            resTrue = 0;     
        }
    }
    else if ((value1 -> type == INT_TYPE) && (value2 -> type == DOUBLE_TYPE)){
        if ((value1 -> i) > (value2 -> d)){
            resTrue = 1;
        }
        else{
            resTrue = 0;     
        }
    }
    else if ((value1 -> type == DOUBLE_TYPE) && (value2 -> type == INT_TYPE)){
        if ((value1 -> d) > (value2 -> i)){
            resTrue = 1;
        }
        else{
            resTrue = 0;     
        }
    }
    else if ((value1 -> type == DOUBLE_TYPE) && (value2 -> type == DOUBLE_TYPE)){
        if ((value1 -> d) > (value2 -> d)){
            resTrue = 1;
        }
        else{
            resTrue = 0;     
        }
    }
    if (resTrue == 1){
        result -> s[0] = '#';
        result -> s[1] = 't';
        result -> s[2] = '\0';
    }
    else{
        result -> s[0] = '#';
        result -> s[1] = 'f';
        result -> s[2] = '\0';   
    }
    return result;
}

Value *primNull(Value *args){
    Value *result = talloc(sizeof(Value));
    result -> s = talloc(sizeof(char)*3);
    result -> type = BOOL_TYPE;

    if (args -> type == NULL_TYPE){
        printf("Evaluation error: no arguments supplied to null?\n");
        texit(0);
    }
    if (args -> c.cdr -> type != NULL_TYPE) {
        printf("Evaluation error: cons takes two arguments, three or more supplied.\n");
        texit(0);
    }
    if(args -> c.car -> type == NULL_TYPE) {
        result -> s[0] = '#';
        result -> s[1] = 't';
        result -> s[2] = '\0';
    }
    else{
        result -> s[0] = '#';
        result -> s[1] = 'f';
        result -> s[2] = '\0';
    }
    return result;
}

Value *primCar(Value *args){
    if (args -> c.cdr -> type != NULL_TYPE){
        printf("Evaluation error: car takes one argument\n");
        texit(0);
    }
    if (args -> type != CONS_TYPE){
        printf("arg type should be cons");
        texit(0);
    }
    Value *concell = args -> c.car;
    if (concell -> type != CONS_TYPE){
        printf("Evaluation error: car takes a pair\n");
        texit(0);
    }
    return concell -> c.car;
}

Value *primCdr(Value *args){
    if (args -> c.cdr -> type != NULL_TYPE){
        printf("cdr should be null");
        texit(0);
    }
    if (args -> type != CONS_TYPE){
        printf("arg type should be cons");
        texit(0);
    }
    // if (args -> c.cdr -> type == NULL_TYPE){
    //     printf("Evaluation error: no arguments supplied to cdr\n");
    //     texit(0);
    // }
    Value *concell = args -> c.car;
    if (concell -> type != CONS_TYPE){
        printf("should be cons");
        texit(0);
    }
    if (concell -> c.cdr -> c.car -> type == DOT_TYPE){
        return concell -> c.cdr -> c.cdr -> c.car;
    }
    return concell -> c.cdr;
}
// end of primitives code //

void displayTrees(Value* list){
    Value *original = list;
    Value *copy = original;

    while (original -> type != NULL_TYPE) { // dave recommended changing to while not null type
        Value *copy = original;
        if (original -> type == CONS_TYPE) {
            copy = copy -> c.car;
        }
        switch (copy -> type){
            case CONS_TYPE:
                printf("(");
                displayTrees(copy);
                printf(")\n");
                break;
            case NULL_TYPE:
                printf("()");
                break;
            case DOT_TYPE:
                printf(" . ");
                break;
            case INT_TYPE:
                printf("%i ", copy -> i);
                break;
            case DOUBLE_TYPE:
                printf("%lf ", copy -> d);
                break;
            case OPEN_TYPE:
                printf("%s ", copy -> s);
                break;
            case CLOSE_TYPE:
                printf("%s ", copy -> s);
                break;
            case STR_TYPE:
                printf("%s ", copy -> s);
                break;
            case BOOL_TYPE:
                printf("%s ", copy -> s);
                break;
            case SYMBOL_TYPE:
                printf("%s ", copy -> s);
                break;
            case VOID_TYPE:
                break;
            case CLOSURE_TYPE:
                printf("#<procedure>\n");
                break;
            default:
                break;
        }
        original = original -> c.cdr;
    }
    printf("\n");
}

void interpret(Value *tree) {
    Frame *newFrame = talloc(sizeof(Frame)); // make a new frame - a struct that has two pointers - parent + bindings
    newFrame -> parent = NULL; 
    newFrame -> bindings = makeNull(); // creates a val that has a null type

    bind("=", primEqual, newFrame);
    bind(">", primGreater, newFrame);
    bind("<", primLess, newFrame);
    bind("-", primSubtract, newFrame);
    bind("+", primAdd, newFrame);
    bind("car", primCar, newFrame);
    bind("cdr", primCdr, newFrame);
    bind("cons", primCons, newFrame);
    bind("null?", primNull, newFrame);
    
    Value *treeptr = tree; // making a pointer to the tree 
    Value *endvalue = makeNull(); // null at first, but will be updating
    while (treeptr -> type == CONS_TYPE) { 
        endvalue = cons(eval(car(treeptr), newFrame), endvalue); // put together the current value and add a null type to the end
        treeptr = treeptr -> c.cdr; // get the next value
    }
    Value *reversed = reverse(endvalue);
    displayTrees(reversed); // print out the new linked list
}

Value *evalIf(Value *args, Frame *frame) {
    // Value *ptrArgs = talloc(sizeof(Value));
    Value *ptrArgs;
    ptrArgs = args;
    if (ptrArgs -> c.car -> type == BOOL_TYPE) {
        if (strcmp(ptrArgs -> c.car -> s, "#t") == 0) { // it is a true boolean statement
            return eval(ptrArgs -> c.cdr -> c.car, frame); // evaluate the car of the cdr 
        }
        else if (ptrArgs -> c.cdr -> c.cdr -> type == NULL_TYPE) { // there is a edge case if the bool type is #f but there is only 1 parameter
            printf("Not enough parameters.");
            texit(0);
        }
        else {
            return eval(ptrArgs -> c.cdr -> c.cdr -> c.car, frame); // evaluate the car of the cdr cdr (draw out the parse tree)
        }
    }
    if (ptrArgs -> c.car -> type == SYMBOL_TYPE) { // you know that it is a symbol
        Value *resultofeval = eval(ptrArgs -> c.car, frame); // call eval -> eval will look for what the symbol is, or if it exists
        if (resultofeval -> type == BOOL_TYPE) {
            if(strcmp(resultofeval -> s, "#t") == 0) {
                return eval(ptrArgs -> c.cdr -> c.car, frame);
            }
            else {
                return eval(ptrArgs -> c.cdr -> c.cdr -> c.car, frame);
            }
        }
        else {
            printf("Symbol is not valid");
            texit(0);
        }
    }
    if (ptrArgs -> c.cdr -> type == NULL_TYPE) {
        printf("Not valid, there are not enough parameters");
        texit(0);
    }
    return ptrArgs;
}

Value *evalLet(Value *args, Frame *frame) {
    Value *middle = args -> c.car;
    Frame *newFrameForLet = talloc(sizeof(Frame));
    newFrameForLet -> bindings = makeNull();
    newFrameForLet -> parent = frame;
    if (middle -> type == NULL_TYPE) {
        return eval(args -> c.cdr -> c.car, newFrameForLet);
    }   
    while (middle -> type != NULL_TYPE) { 
        Value *firstvalofbinding = newFrameForLet -> bindings; // this is after the while loop bc we want to point at the start, since new vals are added in
        while (firstvalofbinding -> type != NULL_TYPE) { 
            if (strcmp(firstvalofbinding -> c.car -> c.car -> s, middle -> c.car -> c.car -> s) == 0) { // a symbol exists in the frame already, cant have duplicates
                printf("This symbol already exists within the frame 117");
                texit(0);
            }
            firstvalofbinding = firstvalofbinding -> c.cdr; // check the next val in the binding
        }
        if (middle -> c.car -> c.car -> type != SYMBOL_TYPE) {
            printf("Error. The first parameter needs to be a symbol 123");
            texit(1);
        }
        else { // we found a symbol type
            if (middle -> c.car -> c.cdr -> type != CONS_TYPE) {
                printf("Error. This is not a cons cell 128");
                texit(1);
            }
            else { // we found a cons type
                Value *resultofeval = eval(middle -> c.car -> c.cdr -> c.car, frame); // value associated with the symbol
                Value *newItems = cons(middle -> c.car -> c.car, resultofeval); // cons together the symbol and the actual value associated with it
                newFrameForLet -> bindings = cons(newItems, newFrameForLet -> bindings); // update the new frame
            }
        }
        middle = middle -> c.cdr;
    }
    args = args->c.cdr;
    return eval(args -> c.car, newFrameForLet);
}

Value *evalDefine(Value *args, Frame *frame){
    if (args -> type == NULL_TYPE){
        printf("Eval error. There are no args to be found after 'define'");
        texit(0);
    }
    if (args -> c.car -> type != SYMBOL_TYPE){
        printf("Eval error. The first input after define has to be a symbol type");
        texit(0);
    }
    if (args -> c.cdr -> type == NULL_TYPE){
        printf("Eval error. Too less parameters.");
        texit(0);
    }
    if (args -> c.cdr -> c.cdr -> type != NULL_TYPE){
        printf("Eval error. Too many parameters for define. It can only have two");
        texit(0);
    }
    Value *voiding = talloc(sizeof(Value));
    voiding -> type = VOID_TYPE; 

    Value *var = args -> c.car; // get the variable or symbol
    Value *expr = eval(args -> c.cdr -> c.car, frame); // get the value associated w the variable
    Value *items = cons(var, expr); // put them together
    frame -> bindings = cons(items, frame->bindings); // update the binding w the new items

    return voiding; 
}

Value *evalLambda(Value *args, Frame *frame){ 
    if (args -> type == NULL_TYPE) {
        printf("Evaluation error: no args following lambda.\n");
        texit(0);
    }
    if (args -> c.cdr -> type == NULL_TYPE) {
        printf("Evaluation error: no code in lambda following parameters.\n");
        texit(0);
    }
    if ((args -> c.car -> type != NULL_TYPE) && (args -> c.car -> type != CONS_TYPE)) {
        printf("Evaluation erro2");
        texit(0);
    }

    Value *ptrtoargs = args -> c.car; // parameters
    while (ptrtoargs -> type != NULL_TYPE){ 
        Value *nextval = ptrtoargs -> c.cdr;
        if (ptrtoargs -> c.car -> type != SYMBOL_TYPE){
            printf("Evaluation error: formal parameters for lambda must be symbols.\n");
            texit(0);
        }
        while (nextval -> type != NULL_TYPE){ // while there are following parameters
            if (strcmp(ptrtoargs -> c.car -> s, nextval -> c.car -> s) == 0){ // checking if the parameters in lambda are the same
                printf("Evaluation error: duplicate identifier in lambda.\n");
                texit(0);
            }
            nextval = nextval -> c.cdr;
        }
        ptrtoargs = ptrtoargs -> c.cdr;
    }

    Value *lambda = talloc(sizeof(Value));
    lambda -> type = CLOSURE_TYPE;

    lambda -> cl.frame = frame; // update frame
    lambda -> cl.functionCode = args -> c.cdr -> c.car; // this is the code in the closure
    lambda -> cl.paramNames = args -> c.car; // these are the parameters

    return lambda;
}

Value *apply(Value *function, Value *args){
    Value *gothroughargs = args;
    Value *gothroughfunc = function -> cl.paramNames;
    Frame *newframe = talloc(sizeof(Frame));
    newframe -> parent = function -> cl.frame;
    newframe -> bindings = makeNull();
    while ((gothroughargs -> type != NULL_TYPE) && (gothroughfunc -> type != NULL_TYPE)) { // while both have values
        Value *pairing = cons(gothroughfunc -> c.car, gothroughargs -> c.car); // put together one and one
        newframe -> bindings = cons(pairing, newframe -> bindings); // update the bindings with new pairs
        gothroughfunc = gothroughfunc -> c.cdr; // next val
        gothroughargs = gothroughargs -> c.cdr; // next val
    }
    if ((gothroughargs -> type == NULL_TYPE) && (gothroughfunc -> type == NULL_TYPE)) { // at the end of the while, both should be null, no vals left
        return eval(function -> cl.functionCode, newframe);
    }
    else {
        printf("Evaluation Error");
        texit(0);
    }
    return gothroughargs;
}

Value *lookUpSymbol(Value *tree, Frame *frame){ // if the symbol exists, return the value
    Value *seeker;
    seeker = frame -> bindings; // points to the first cons cell of the frame
    while (seeker -> type != NULL_TYPE) {
        if (strcmp(seeker -> c.car -> c.car -> s, tree -> s) == 0) {
            // return eval(seeker -> c.car -> c.cdr, frame);
            return seeker -> c.car -> c.cdr;
        }
        seeker = seeker -> c.cdr;
    }
    if (frame -> parent == NULL) { // if the parent type is null, it does not exist
        printf("Evaluation error: symbol not found.\n");
        texit(0);
    }
    else { 
       return lookUpSymbol(tree, frame -> parent); // search through the parent
    }
    return seeker;
}

Value *eval(Value *tree, Frame *frame) {
   switch (tree->type)  {
     case INT_TYPE: {
        return tree;
        break;
     }
     case DOUBLE_TYPE: {
        return tree;
        break;
     }  
     case STR_TYPE: {
        return tree;
        break; 
     }
     case CLOSURE_TYPE: {
        return tree;
        break;
     }
     case NULL_TYPE: {
        break;
     }
     case BOOL_TYPE: {
        return tree;
        break;
     }
     case SYMBOL_TYPE: {
        return lookUpSymbol(tree, frame); // node is a symbol type
        break;
     }  
     case PRIMITIVE_TYPE: {
        return tree;
        break;
     }
     case CONS_TYPE: {
        Value *first = car(tree);
        Value *args = cdr(tree);
        if (first -> type != SYMBOL_TYPE) {
            if (first -> type != CONS_TYPE){
                printf("Evaluation Error. The type is not a symbol type");
                texit(0);
            }
        }
        if (first -> type == CONS_TYPE) {
            Value *firsteval = eval(first,frame);
            if (firsteval -> type == CLOSURE_TYPE) {
                return apply(firsteval, args);
            }
        }

        if (strcmp(first->s,"if") == 0) {
            return evalIf(args,frame);
        }
        
        else if (strcmp(first->s,"let") == 0) { 
            if (args -> c.cdr -> type == NULL_TYPE) {
                printf("Too few parameters 221");
                texit(0);
            }
            return evalLet(args,frame);
        }

        else if (strcmp(first->s,"letrec") == 0) { 
            if (args -> c.cdr -> type == NULL_TYPE) {
                printf("Too few parameters 221");
                texit(0);
            }
            return evalLet(args,frame);
        }
        else if (strcmp(first->s,"begin") == 0) {
            return evalBegin(args,frame);
        }
        else if (strcmp(first->s, "quote") == 0) {
             if (args->type != CONS_TYPE) {
                printf("Evaluation Error. 'quote' requires one argument.\n");
                texit(0);
            }
            else if (args -> c.cdr -> type != NULL_TYPE) {
                printf("Evaluation Error. Not a proper quote function. Too many parameters\n");
                texit(0);
            }
            else if (args -> type == NULL_TYPE) {
                printf("Synax error. Not a proper quote function. Not enough paramenters 286\n");
                texit(0);
            }
            else {
                return args -> c.car;
            }
        }

        else if (strcmp(first->s, "define") == 0) {
            return evalDefine(args, frame);
        }

        else if (strcmp(first->s, "lambda") == 0) {
            return evalLambda(args, frame);
        }

        else if (strcmp(first->s, "set!") == 0) {
            return evalSet(args, frame);
        }

        else {
            Value *function = lookUpSymbol(first, frame);
            if (function -> type == CLOSURE_TYPE) {
                Value *trackargs = args;
                while (trackargs -> type != NULL_TYPE) {
                    Value *evaluatingnext = eval(trackargs -> c.car, frame);
                    trackargs -> c.car = evaluatingnext;
                    trackargs = trackargs -> c.cdr;
                }

            }
            else if (function -> type == PRIMITIVE_TYPE) {
                Value *trackargs = args;
                while (trackargs -> type != NULL_TYPE) {
                    Value *evaluatingnext = eval(trackargs -> c.car, frame);
                    trackargs -> c.car = evaluatingnext;
                    trackargs = trackargs -> c.cdr;
                }
                return function->pf(args);
            }
        }
        break;
     }
     default: {
        printf("Error. Type not found");
        texit(0);
     }
   }
   return tree;
}