#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <typeinfo>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;

//#define DDD

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}


/* Least common object in the tree. */
Symbol TreeNode::lub(TreeNode *root, Symbol t1, Symbol t2)
{

                if (!t1)
                        return t2;
                TreeNode *t1node;
                TreeNode *t2node;

                if (comp_two_type(t1, Object) || comp_two_type(t2, Object))
                        return Object;

                t1node = root->get(this, t1);
                do {
                        t2node = t1node->get(this, t2);
                        t1node = root->get(this, t1node->parent);
                } while ( t2node == NULL
                          && ((t1node = root->get(this, t1node->parent)) != NULL));

                if (t1node == NULL)
                        return NULL;
                else
                        return t1node->node_name;
        }


// Clases -> Classes_class -> list_node<Class_> --> Class__class : public tree_node:tree.h


ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr), _root(classes) {
    _globalmap = new GlobalSymbolTable();
    classTreeRoot = new TreeNode(Object, NULL);
    _globalmap->enterscope();
//    install_basic_classes();
    first_pass();
    second_pass();

    if (_globalmap->lookup(Main) == NULL) {
        error_stream << "Class Main is not defined.\n";
        semant_error();
    }
    
    _globalmap->exitscope();
}

void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);

    int ret;
    ret = classTreeRoot->addchild(Str, Object);
    ret |= classTreeRoot->addchild(Bool, Object);
    ret |= classTreeRoot->addchild(Int, Object);
    ret |= classTreeRoot->addchild(IO, Object);

    access_class(Object_class);
    access_class(Bool_class);
    access_class(IO_class);
    access_class(Int_class);
    access_class(Str_class);
    
//#define TREENODE_SELF_TEST
#ifdef TREENODE_SELF_TEST
    cout << "add result: " << ret << endl;
    cout << "Str is Object subclass: " << classTreeRoot->isSubClass(Str, Object) << " expecting : True" << endl;
    cout << "IO is Object subclass: " << classTreeRoot->isSubClass(IO, Object) << " expecting : True" << endl;
    cout << "Object is IO subclass:" << classTreeRoot->isSubClass(Object, IO) << " expecting : False" << endl;
    cout << "Str is IO subclass:" << classTreeRoot->isSubClass(Str, IO) << " expecting: False" << endl;
#endif
    
    
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{
//    abort();
    return semant_error(c->get_filename(),c);
}

ostream& ClassTable::semant_error(Class_ c, const char *errormsg)
{
    error_stream << c->get_filename() << ":"
                 << c->get_line_number() << ": "
                 << errormsg;

    return semant_error();
}

ostream& ClassTable::semant_error_line(Class_ c) {
    error_stream << c->get_filename() << ":"
                 << c->get_line_number() << ": ";
    return error_stream;
}



void ClassTable::access_attr(Class_ c,
                             attr_class *attr, ClassSymbolTable *t) {
    // Because this is a init, we should record the attr 's name and
    // type in the type system.

    if (pass == 1 && strcmp(attr->get_name()->get_string(), "self") == 0)
        semant_error(c, "'self' cannot be the name of an attribute.\n");

    if (pass == 1 && findSymbolToObject(dynamic_cast<class__class *>(c)->get_name(),
                                        attr->get_name())) {
            semant_error_line(c);
            error_stream << "Attribute " << attr->get_name() << " is an attribute of an inherited class.\n";
            semant_error();
        }
    
    if (t->probe(attr->get_name()) != NULL) {
        if (pass == 1)
            semant_error(c);
    } else {
#ifdef DUMP_DECLEAR
        cout << " Class: " << dynamic_cast<class__class *>(c)->get_name()
             << "  declear attr: " << attr->get_name()
             << "  type: " << attr->get_type_decl() << endl;
#endif
        Symbol type = attr->get_type_decl();
        t->addid(attr->get_name(), type);
        
    }
    if (!attr->get_init()->is_no_expr()) {
        Symbol initType = access_expr(c, attr->get_init(), t);
        if (initType == 0) {
//            cout << "expr is null ? " << endl;
            return;
        }
        if (!comp_two_type(initType, SELF_TYPE)
            && !comp_two_type(initType, attr->get_type_decl())
            && !classTreeRoot->isSubClass(initType,
                                          attr->get_type_decl())) {
            semant_error(c);
        }
    }
}

inline Symbol ClassTable::self_type_c(Class_ c) {
    class__class *cc = dynamic_cast<class__class *>(c);
    return cc->get_name();
}

inline int comp_two_type(Symbol a, Expression expr)
{
    if (expr->get_type() == NULL) {
        cout << "compare with no_type..., symbol:" << a << endl;
        return false;
    }
    return a->equal_string(expr->get_type()->get_string(), expr->get_type()->get_len());
}


Symbol ClassTable::findSymbolToObject(Symbol node, Symbol method_or_attr) {
    // 1. get parent.
    // 2. check if parent is Object
    //  if it's null or object, return NULL.
    // if not object, check whether this have such symbol
    // if have , return it's type,
    //
    Symbol t = NULL;
    if (node == NULL)
        return NULL;

//    cout << "find " << method_or_attr << " in " << node << endl;
    ClassSymbolTable *table = _globalmap->lookup(node);
    if (table)
        t = table->lookup(method_or_attr);
    if (t)
        return t;
        
    TreeNode *p = classTreeRoot->get(classTreeRoot, node);
    if (!p)
        return NULL;
    return (findSymbolToObject(p->get_parent(), method_or_attr));
}

Symbol ClassTable::access_dispatch_and_static(Class_ c, static_dispatch_class *static_c ,
                                              dispatch_class *dis_c, ClassSymbolTable *t)
{
    Expressions es;
    Symbol static_type = NULL;                 // Static type name for static dispatch.
    Symbol call_object_type, call_object_type_copy;
    Symbol body_return_type;
    Expression  expr;
    ClassSymbolTable *typetable;
    Symbol function_ret = NULL;
    Symbol curClassType = dynamic_cast<class__class *>(c)->get_name();
    Symbol callableid = NULL;
    Expression cure;

    if (static_c) {
        cure = static_c;
        static_dispatch_class *ee = static_c;
        es = ee->get_actual();
        static_type = ee->get_type_name();
        expr = ee->get_expr();
        callableid = ee->get_name();
    } else if (dis_c) {
        cure = dis_c;
        dispatch_class *ee = dis_c;
        es = ee->get_actual();
        expr = ee->get_expr();
        callableid = ee->get_name();
    }
    
    for (int i = es->first(); es->more(i); i = es->next(i)) {
        body_return_type = access_expr(c, es->nth(i), t);
    }

    call_object_type = access_expr(c, expr, t);
    call_object_type_copy = call_object_type;

    if (comp_two_type(call_object_type, SELF_TYPE)) {
        call_object_type = dynamic_cast<class__class *>(c)->get_name();
    }

    if (static_type) {
        typetable = _globalmap->lookup(static_type);
        function_ret = findSymbolToObject(static_type, callableid);
    } else {
        typetable = _globalmap->lookup(call_object_type);
        function_ret = findSymbolToObject(call_object_type, callableid);
    }

    
    if (comp_two_type(function_ret, SELF_TYPE)
        && !comp_two_type(call_object_type_copy, SELF_TYPE))
        function_ret = call_object_type;

    if (function_ret == 0 && pass == 2) {

        cout << "dispatch: cant find :"
             << call_object_type << " . "
             << callableid << " 's define" << endl; 
        semant_error(c);
        return Object;
    }

    cure->set_type(function_ret);
    return function_ret;
    
}

Symbol ClassTable::access_expr(Class_ c, Expression_class *e, ClassSymbolTable *t )
{
    // Assign.
    if (typeid(*e) == typeid(assign_class)) {
        assign_class *ee = dynamic_cast<assign_class *>(e);
        if (ee == 0) {
            cout << "error" << endl;
        }

        if (strcmp(ee->get_name()->get_string(), "self") == 0) {
            if (pass == 1) {
                semant_error_line(c) << "Cannot assign to 'self'.\n";
                semant_error();
            }
            ee->set_type(Object);
            return Object;
        }
        Symbol class_type = dynamic_cast<class__class *>(c)->get_name();
        Symbol ty = findSymbolToObject(class_type, ee->get_name());
        if (ty == NULL) {
            if (pass == 2) {
                // not found define.
                error_stream << "not found define:" << ee->get_name() << endl;
                semant_error(c);
            }
            ee->set_type(Object);
            return Object;
        } else {
            // Needs access the expr first.
            Symbol init_return_type = access_expr(c, ee->get_expr(), t);
            if (comp_two_type(ty, init_return_type)) {
                ee->set_type(init_return_type);
                return init_return_type;
            } else {
                if (pass == 2) {
                    error_stream << c->get_filename() << ":"
                                 << c->get_line_number() << ": "
                                 << "Type " << ee->get_expr()->get_type()
                                 << " of assigned expression does not conform to declared type "
                                 << ty <<" of identifier "
                                 << ee->get_name() << "." << endl;
                    semant_error();
                    ee->set_type(Object);
                }
            }
            return Object;
        }
    }

    // Static dispatch and dispatch.
    else if (typeid(*e) == typeid(static_dispatch_class)) {
        static_dispatch_class *ee = dynamic_cast<static_dispatch_class *>(e);
        return access_dispatch_and_static(c, ee, NULL, t);
    } else if (typeid(*e) == typeid(dispatch_class)) {
        dispatch_class *ee = dynamic_cast<dispatch_class *>(e);
        return access_dispatch_and_static(c, NULL, ee, t);
    }
    // Cond
    else if (typeid(*e) == typeid(cond_class)) {
        cond_class *ee = dynamic_cast<cond_class *>(e);
        Symbol tt = access_expr(c, ee->get_pred(), t);
        if (pass == 2 && !comp_two_type(tt, Bool)) {
            semant_error(c);
            ee->set_type(Object);
        }
        Symbol t1 = access_expr(c, ee->get_then_exp(), t);
        Symbol t2 = access_expr(c, ee->get_else_exp(), t);
        Symbol tr = classTreeRoot->lub(classTreeRoot, t1, t2);
        ee->set_type(tr);
        return tr;
    }
    // Loop
    else if (typeid(*e) == typeid(loop_class)) {
        loop_class *ee = dynamic_cast<loop_class *>(e);
        Expression pred = ee->get_pred();
        Expression body = ee->get_body();
        Symbol type = access_expr(c, pred, t);
        if (pass == 2 && !comp_two_type(type, Bool)) {
            semant_error(c);
            ee->set_type(Object);
        }
        access_expr(c, body, t);
        ee->set_type(Object);
        return Object;
    }
    // typcase
    else if (typeid(*e) == typeid(typcase_class)) {
        typcase_class *ee = dynamic_cast<typcase_class *>(e);
        Symbol t1 = access_expr(c, ee->get_expr(), t);
        Cases cs = ee->get_cases();
        Symbol type = NULL;
        for (int i = cs->first(); cs->more(i); i = cs->next(i)) {
            branch_class *eee = dynamic_cast<branch_class *>(cs->nth(i));
            t->enterscope();
            t->addid(eee->get_name(), eee->get_type_decl());
            type = classTreeRoot->lub(classTreeRoot, type,
                                       access_expr(c, eee->get_expr(), t));
            t->exitscope();
        }

        e->set_type(type);
        return type;
    }
    // block
    else if (typeid(*e) == typeid(block_class)) {
        Expressions es = dynamic_cast<block_class *>(e)->get_body();
        Symbol type = NULL; 
        t->enterscope();
        for (int i = es->first(); es->more(i); i = es->next(i))
            type = access_expr(c, es->nth(i), t);
        t->exitscope();
        e->set_type(type);
        return type;
    }
    // Let
    else if (typeid(*e) == typeid(let_class)) {
        let_class *ee = dynamic_cast<let_class *>(e);
        // SELF

        if (strcmp(ee->get_identifier()->get_string(), "self") == 0) {
            if (pass == 1) {
                semant_error_line(c) << "'self' cannot be bound in a 'let' expression.\n";
                semant_error();
            }
            return Object;
        }
            
        Symbol t0 = ee->get_type_decl();
        Symbol t1 = access_expr(c, ee->get_init(), t);

        t->enterscope();
        t->addid(ee->get_identifier(), t0);
        
        if (t1) {
            if (!comp_two_type(t0, t1)) {
                if (pass == 2) {
                    semant_error_line(c) << "Inferred type "
                                         << t1
                                         <<  " of initialization of "
                                         << ee->get_identifier()
                                         << " does not conform to identifier's declared type "
                                         << t0 << ".\n";
                    semant_error();
                    return Object;
                }
            }
        }

        Symbol rt = access_expr(c, ee->get_body(), t);

        e->set_type(rt);

        t->exitscope();
        return rt;
    }
    // plus
    // sub_class
    // mul_class
    // divide class
    else if (typeid(*e) == typeid(plus_class)) {
        plus_class *ee = dynamic_cast<plus_class *>(e);
        Symbol t1 = access_expr(c, ee->get_e1(), t);
        Symbol t2 = access_expr(c, ee->get_e2(), t);
        // not same type, or not int is all error.
        if (pass == 2
            && (!comp_two_type(t1, t2)
                || !comp_two_type(Int, t2))) {
            semant_error_line(c) << "non-Int arguments: " << t1 << " + " << t2 << "\n";
            semant_error();
            e->set_type(Object);
            return Object;
        } else {
            e->set_type(t1);
            return t1;
        }
    } else if (typeid(*e) == typeid(sub_class)) {
        sub_class *ee = dynamic_cast<sub_class *>(e);
        Symbol t1 = access_expr(c, ee->get_e1(), t);
        Symbol t2 = access_expr(c, ee->get_e2(), t);
        // not same type, or not int is all error.
        if (pass == 2
            && (!comp_two_type(t1, t2)
                || !comp_two_type(Int, t2))) {
            semant_error(c);
            e->set_type(Object);
            return Object;
        } else {
            e->set_type(t1);
            return t1;
        }
    }

    else if (typeid(*e) == typeid(mul_class)) {
        mul_class *ee = dynamic_cast<mul_class *>(e);
        Symbol t1 = access_expr(c, ee->get_e1(), t);
        Symbol t2 = access_expr(c, ee->get_e2(), t);
        // not same type, or not int is all error.

        if (pass == 2
            && (!comp_two_type(t1, t2)
                || !comp_two_type(Int, t2))) {
            semant_error(c);
            e->set_type(Object);
            return Object;
        } else {
            e->set_type(Int);
            return t1;
        }
    }

    else if (typeid(*e) == typeid(divide_class)) {
        divide_class *ee = dynamic_cast<divide_class *>(e);
        Symbol t1 = access_expr(c, ee->get_e1(), t);
        Symbol t2 = access_expr(c, ee->get_e2(), t);
        // not same type, or not int is all error.

        if (pass == 2
            && (!comp_two_type(t1, t2)
                || !comp_two_type(Int, t2))) {
            semant_error(c);
            e->set_type(Object);
            return Object;
        } else {
            e->set_type(Int);
            return t1;
        }
    }

    
    // neg class
    else if (typeid(*e) == typeid(neg_class)) {
        neg_class *ee = dynamic_cast<neg_class *>(e);
        Symbol tt = access_expr(c, ee->get_e1(), t);
        if (pass == 2 && !comp_two_type(Int, tt)) {
            cout << "tt : " << tt <<endl;
            semant_error(c);
            e->set_type(Object);
            return Object;
        } else {
            e->set_type(tt);
            return tt;
        }
    }
    // eq class
    if( typeid(*e) == typeid(eq_class)) {
        eq_class *ee = dynamic_cast<eq_class *>(e);
        Symbol t1 = access_expr(c, ee->get_e1(), t);
        Symbol t2 = access_expr(c, ee->get_e2(), t);

        if (isInternalClassName(t2) || isInternalClassName(t1)) {
            if (!comp_two_type(t1, t2)) {
                semant_error_line(c);
                error_stream << "Illegal comparison with a basic type.\n";
                semant_error();
                e->set_type(Bool);
                return Bool;
            }
        }
        
        e->set_type(Bool);
        return Bool;
    }

    // lt class
    else if (typeid(*e) == typeid(lt_class)) {
        lt_class *ee = dynamic_cast<lt_class *>(e);
        if (ee) {
            Symbol t1 = access_expr(c, ee->get_e1(), t);
            Symbol t2 = access_expr(c, ee->get_e2(), t);
            if (pass == 2 && (!comp_two_type(Int, t1)
                              ||!comp_two_type(Int, t2))) {
                semant_error(c);
                e->set_type(Object);
                return Object;
            } else {
                e->set_type(Bool);
                return Bool;
            }
        }
        // leq class
    } else if (typeid(*e) == typeid(leq_class)) {
        leq_class *ee = dynamic_cast<leq_class *>(e);
        if (ee) {
            Symbol t1 = access_expr(c, ee->get_e1(), t);
            Symbol t2 = access_expr(c, ee->get_e2(), t);
            if (pass == 2 && (!comp_two_type(Int, t1)
                              ||!comp_two_type(Int, t2))) {
                semant_error(c);
                e->set_type(Object);
                return Object;
            } else {
                e->set_type(Bool);
                return Bool;
            }
        }
    }
    
    // comp class
    else if (typeid(*e) == typeid(comp_class)) {
        comp_class *ee = dynamic_cast<comp_class *>(e);
        Symbol tt = access_expr(c, ee->get_e1(), t);
        if (pass == 2 && !comp_two_type(Bool, tt)) {
            semant_error(c);
            e->set_type(Object);
            return Object;
        } else {
            e->set_type(Bool);
            return Bool;
        }
    }
    // int const class
    else if (typeid(*e) == typeid(int_const_class)) {
        e->set_type(Int);
        return Int;
    }
    // bool const class
    else if (typeid(*e) == typeid(bool_const_class)) {
        e->set_type(Bool);
        return Bool;
    }
    // string const class
    else if (typeid(*e) == typeid(string_const_class)) {
        e->set_type(Str);
        return Str;
    }
    // new class
    else if (typeid(*e) == typeid(new__class)) {
        Symbol tt = dynamic_cast<new__class *>(e)->get_type_name();
        if (!comp_two_type(tt, SELF_TYPE)
            && _globalmap->lookup(tt) == NULL) {
            if (pass == 2) {
                semant_error_line(c) << "'new' used with undefined class "
                                 << tt << endl;
                semant_error();
            }
        }
        e->set_type(tt);
        return tt;
    }
    // isvoid class
    else if (typeid(*e) == typeid(isvoid_class)) {
        isvoid_class *ee = dynamic_cast<isvoid_class *>(e);
        access_expr(c, ee->get_e1(), t);
        e->set_type(Bool);
        return Bool;
    }
    // no expr
    // else if (typeid(*e) == typeid(no_expr_class)) {
    //     return Object;
    // }
    // object class
    else if (typeid(*e) == typeid(object_class)) {
        object_class *ee = dynamic_cast<object_class *>(e);

        if (comp_two_type(ee->get_name(), self)) {
            e->set_type(SELF_TYPE);
            return SELF_TYPE;
        } else {
            Symbol cls_name = dynamic_cast<class__class *>(c)->get_name();
            Symbol type = findSymbolToObject(cls_name, ee->get_name());
            if (pass == 2 && type == NULL) {

                error_stream << c->get_filename() << ":"
                             << c->get_line_number() << ": "
                             << "Undeclared identifier "
                             << ee->get_name()
                             << "." << endl;
                e->set_type(Object);
                semant_error();
                return Object;
            }

            e->set_type(type);
            return type;
        }
    }


//    cout << "Warnning: going to end of expr!!! e: " << typeid(*e).name() << endl;
    return 0;
}



void ClassTable::access_method(Class_ c, method_class *m, ClassSymbolTable *t)
{
    currMethodST = new MethodSymbolTable();


    // Add method to this type's symbol table.
    t->addid(m->get_name(), m->get_return_type());
#ifdef DDD
    cout << "define class : " << dynamic_cast<class__class *>(c)->get_name() << " . " << m->get_name() << endl;
#endif

    if (!comp_two_type(m->get_return_type(), SELF_TYPE)) {
        if (pass == 2)
            if (!_globalmap->lookup(m->get_return_type())) {
                semant_error_line(c) << "Undefined return type " << m->get_return_type()
                                    << " in method " << m->get_name() << ".\n";
                semant_error();
            }
    }

    currMethodST->enterscope();

    // process formals to init parameters.
    if (m->get_formals()->len() != 0) {
        Formals f = m->get_formals();
        for (int i = f->first(); f->more(i); i = f->next(i)) {
            formal_class *ff = dynamic_cast<formal_class *>(f->nth(i));
            currMethodST->addid(ff->get_name(), ff->get_type_decl());
            t->addid(ff->get_name(), ff->get_type_decl());
        }
    }
    // Process the expr.
    Symbol tt = access_expr(c, m->get_expr(), t);

    if (tt != NULL && pass == 2) {
        if (!comp_two_type(tt, SELF_TYPE)
                 && !comp_two_type(tt, m->get_return_type())
                 && !classTreeRoot->isSubClass(tt, m->get_return_type())) {

            semant_error_line(c) << "Inferred return type " << tt
                                 << " of method " << m->get_name()
                                 << " does not conform to declared return type "
                                 << m->get_return_type() << ".\n";
            semant_error();

            // Here means, the method 's caller must have such method's class...
            // class a {
            //        method();
            //  }
            //  (new a).method(),
            // the ^^^^ must be a class a...
            // cout << m->get_name() << " two type not equal or less: " << tt
            //      << " return type: " << m->get_return_type() << endl;
                // semant_error(c);
                m->set_return_type(Object);
        } 
    }

    m->set_return_type(m->get_return_type());
    
    currMethodST->exitscope();
    delete currMethodST;
}


void ClassTable::access_features(Class_ c, Features fs, ClassSymbolTable *t)
{

    vector<method_class *> methods;
    typedef vector<method_class *>::iterator VMI;
    for (int i = fs->first(); fs->more(i); i = fs->next(i)) {
        Feature_class * f = fs->nth(i);

#ifdef DDD
        cout << typeid(*f).name() << endl;
#endif

//        if (pass == 1)
//            t->enterscope();
        if (typeid(*f) == typeid(method_class)) {
            methods.push_back(dynamic_cast<method_class *>(f));
        } else if (typeid(*f) == typeid(attr_class)) {
            access_attr(c, dynamic_cast<attr_class *>(f), t);
        }
//        if (pass == 2)
//            t->exitscope();
    }

    for (VMI i = methods.begin(); i != methods.end(); i++)
        access_method(c, *i, t);
}

bool ClassTable::isInternalClassName(Symbol a) {
    return (strcmp(a->get_string(), "Object") == 0
            || strcmp(a->get_string(), "Int") == 0
            || strcmp(a->get_string(), "Bool") == 0
            || strcmp(a->get_string(), "String") == 0);
}

bool ClassTable::invalidParentClassName(Symbol a) {
    return (strcmp(a->get_string(), "Int") == 0
            || strcmp(a->get_string(), "Bool") == 0
            || strcmp(a->get_string(), "String") == 0);
}


void ClassTable::access_class(tree_node* node)
{
    if (typeid(*node) == typeid(class__class)) {

        class__class *a = dynamic_cast<class__class *>(node);

        // Create a symbol table for this class.
        // If the class already exist, report an error.
        if (pass == 1 && _globalmap->lookup(a->get_name()) != NULL) {
            if (isInternalClassName(a->get_name())) {
                semant_error_line(a);
                error_stream << "Redefinition of basic class " << a->get_name() << ".\n";
                semant_error();
            } else {
                semant_error_line(a)
                    << "Class " << a->get_name() << " was previously defined.\n";
                semant_error();
            }
        } else if (pass == 1) {
            _globalmap->addid(a->get_name(), new ClassSymbolTable());
        }

        ClassSymbolTable *t = _globalmap->probe(a->get_name());
        if (pass == 1)
            t->enterscope();
        access_features(a, a->get_features(), t);

//        Not exit scope... orther wise, not find the method...
//        if (pass == 2)
//            t->exitscope();
        
#ifdef DDD
        cout << "name: " << a->get_name() << " parent " << a->get_parent() << "features:" << a->get_features() << endl;
#endif
    }
}

void ClassTable::access_tree_node(Classes class_, ClassTable *classtable)
{

    typedef vector<Class__class *> vc;
    vc failed_first;

    if (pass == 1) {
        for (int i = class_->first(); class_->more(i); i = class_->next(i)) {
            Class_ node = class_->nth(i);
            class__class *cc = dynamic_cast<class__class *>(node);
            Symbol p = cc->get_parent() == NULL ? Object : cc->get_parent();

#ifdef DDD
            cout << "relation: class: " << cc->get_name() << " Parent: "
                 << p << endl;
#endif
            if (!classTreeRoot->addchild(cc->get_name(), p)) {
#ifdef DDD
                cout << "class : " << cc->get_name() << " with parent: " << p
                     << " failed to inherient" << endl;
#endif
                failed_first.push_back(cc);
            }
        }
    }

    install_basic_classes();

    for (vc::iterator i = failed_first.begin(); i != failed_first.end(); i++) {
        class__class *cc = dynamic_cast<class__class *>(*i);
        Symbol p = cc->get_parent() == NULL ? Object : cc->get_parent();

        // Check whether inherient from basic class.
        if (pass == 1 &&
            invalidParentClassName(cc->get_parent())) {
            semant_error_line(cc) << "Class " << cc->get_name()
                                  << " cannot inherit class "
                                  << cc->get_parent() << ".\n";
            semant_error();
        }

        if (pass == 1)  {
            if (!classTreeRoot->get(classTreeRoot, cc->get_parent())) {
                semant_error_line(cc) << "Class " << cc->get_name()
                                      << " inherits from an undefined class "
                                      << cc->get_parent() << ".\n";
                semant_error();
            }
        }
        
        if (pass == 1 && !classTreeRoot->addchild(cc->get_name(), p)) {
        }
    }
    
    for (int i = class_->first(); class_->more(i); i = class_->next(i)) {
        Class_ node = class_->nth(i);
#ifdef DDD
        cout << class_->nth(i) << endl;
#endif
        access_class(class_->nth(i));
    }
}

void ClassTable::second_pass() {
    pass = 2;
    access_tree_node(_root, this);
}
void ClassTable::first_pass() {
    pass = 1;
    access_tree_node(_root, this);
    return;
}


ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;
//    abort();
    return error_stream;
} 


/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */



void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    ClassTable *classtable = new ClassTable(classes);

    /* some semantic analysis code may go here */


    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    }
}


