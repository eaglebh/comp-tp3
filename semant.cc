

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <tr1/functional>
#include "semant.h"
#include <algorithm>
#include "utilities.h"

#define DBGLINE if(semant_debug) cout << __FILE__ << ":" << __LINE__ << endl;

extern int semant_debug;
extern char *curr_filename;

ClassTable* clsTablePtr = NULL;
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



ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {

    /* Fill this in */
    m_classList = classes;
    install_basic_classes();
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

    m_classList = append_Classes(m_classList, single_Classes(Object_class));
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

    m_classList = append_Classes(m_classList, single_Classes(IO_class));

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    m_classList = append_Classes(m_classList, single_Classes(Int_class));

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);
    m_classList = append_Classes(m_classList, single_Classes(Bool_class));

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

    m_classList = append_Classes(m_classList, single_Classes(Str_class));

    if (semant_debug)
        cout << "classes list: " << m_classList->len() << endl;
}


//helper class to report errors by symbol name
Class_ ClassTable::find_class_by_name(Symbol name){
    Class_ c;
    for(int i = 0; i < m_classList->len(); i++){
        c = m_classList->nth(i);
        class__class* cls = static_cast<class__class*>(c);
        if (cls->get_name() == name){
            return c;
        }
    }
    return 0;
}

bool ClassTable::do_check(){
    return check_class_relations() && check_types();
}


namespace{
    bool isVisited(const ClassVisitInfo& info){
        return info.visit > 0;
    }

    bool beginsWith(const ClassNameList& ancestors, const Symbol& name){
        return *(ancestors.begin()) == name;
    }
}

bool ClassTable::check_class_relations() {
    if (semant_debug)
        cout << "checking inheritence..." << endl;
    //check for inheritance graph
    ClassVisitInfo info;
    for (int i = 0; i < m_classList->len(); i++) {
        class__class* cls = static_cast<class__class*>(m_classList->nth(i));
        if (cls->get_name() == SELF_TYPE){
            semant_error(cls) << endl;
            continue;
        }
        info.name = cls->get_name();
        info.parent = cls->get_parent(); 
        info.visit = 0;
        m_visitGraph.push_back(info);
        m_classNameList.push_back(info.name);
    }
    if (semant_debug)
        cout << "classes list size:" << m_visitGraph.size() << endl;

    //check parent existence first because of dependency
    for (VisitCIt it = m_visitGraph.begin(), itEnd = m_visitGraph.end();
            it != itEnd; ++it){
        const Symbol& parent = it->parent;
        if (semant_debug)
            cout << "Checking on " << it->name << endl;

        // 1. It's an error to redefine basic classes
        if ((it->name == Int) || (it->name == Bool) || (it->name == Str)
                || (it->name == IO) || (it->name == Object)){
            Class_ cls = find_class_by_name(it->name);
            if (cls->get_filename() != stringtable.lookup_string("<basic class>")){
                if (semant_debug)
                    cout << "Redefined Int/Bool/String/IO/Object found!" << endl;
                semant_error(find_class_by_name(it->name)) << "Redefinition of basic class " << it->name << ".\n";
                return false;
            }
        }
        // 2. It's an error to inherit from Int/Bool/String
        if (parent == Int || parent == Bool || parent == Str){
            if (semant_debug)
                cout << "Inherit from builtin Int/Bool/String found!" << endl;
            semant_error(find_class_by_name(it->name)) << "Class " << it->name
                << " cannot inherit class " << parent << ".\n";
            return false;
        }
        // 3. Parent class must be defined
        if ((std::find(m_classNameList.begin(), m_classNameList.end(), parent) == \
                m_classNameList.end()) && (parent != No_class)){
            if (semant_debug)
                cout << "Parent class not existed!" << endl;
            semant_error(find_class_by_name(it->name)) << "Class " << it->name 
                << " inherits from an undefined class " << it->parent << ".\n";
            return false;
        }
    }

    if (semant_debug)
        cout << "Parent check succeed!" << endl;

    //class name should be unique
    bool has_main = false;
    for (size_t i = 0; i < m_classNameList.size(); ++i){
        if (std::count(m_classNameList.begin(), m_classNameList.end(), m_classNameList[i]) != 1){
            if (semant_debug)
                cout << "class name conflict!" << endl;
            semant_error(find_class_by_name(m_classNameList[i])) << "Class " << m_classNameList[i] << " was previously defined.\n";
            return false;
        }
        if (Main == m_classNameList[i]){
            has_main = true;
        }
    }

    //main class should be declared
    if (!has_main){
        semant_error() << "Class Main is not defined." << endl;
    }

    //check for cycles and record ancestors
    size_t maxVisitLength = m_classNameList.size();
    size_t depth = 0;
    ClassVisitList nonVisited(m_visitGraph);
    ClassNameList ancestors;

    while (!nonVisited.empty()){
        ancestors.clear();
        depth = 1;
        ClassVisitInfo& node = *(nonVisited.begin());
        ancestors.push_back(node.name);

        //Mark the node to exclude for next round
        for (VisitIt it = m_visitGraph.begin(), itEnd = m_visitGraph.end();
                it != itEnd; ++it){
            if (it->name == node.name){
                it->visit++;
            }
        }

        while (node.parent != No_class){
            ancestors.push_back(node.parent);
            //parent existence is assured before
            for (VisitIt it = m_visitGraph.begin(), itEnd = m_visitGraph.end();
                it != itEnd; ++it){
                if (it->name == node.parent){
                    node = (*it);
                    break;
                }
            }
            depth++;

            if (depth >= maxVisitLength){
                //cycles detected!
                semant_error(find_class_by_name(node.name));
                if (semant_debug){
                    cout << "cycle found! depth:" << depth << "maxLength:" << maxVisitLength << endl;
                }
                return false;
            }
        }

        //If parent is not defined, default to object
        if ((node.name != Object) && (node.parent == No_class)){
            ancestors.push_back(Object); 
        }
        m_pathList.push_back(ancestors);

        //Since a path is found, now re-count the nonvisited nodes
        nonVisited.clear();
        std::remove_copy_if(m_visitGraph.begin(), m_visitGraph.end(), std::back_inserter(nonVisited), isVisited);
        //if (semant_debug){
        //    cout << "After one round, visited depth = " << depth << ", remaining nodes = " << nonVisited.size() << endl;
        //}
    }

    //build ancestors map
    for(AncestorsPathList::iterator it = m_pathList.begin(), itEnd = m_pathList.end();
            it != itEnd; ++it){
        for (ClassNameList::iterator itNames = it->begin(), itNamesEnd = it->end(); 
                itNames != itNamesEnd; ++itNames){
            Symbol clsName = *itNames;
            if (m_ancestorsTable.find(clsName) == m_ancestorsTable.end()){
                //build one trace
                AncestorsPathList::iterator itTrace = std::find_if(m_pathList.begin(), m_pathList.end(), 
                        std::tr1::bind(&beginsWith, std::tr1::placeholders::_1, clsName));
                if (itTrace != itEnd){
                    m_ancestorsTable[clsName] = &(*itTrace);
                }else{
                    //Using the trace of this path, need to save the path first!
                    size_t offset = std::distance(m_pathList.begin(), it);
                    ClassNameList ancestors(itNames, itNamesEnd);
                    m_pathList.push_back(ancestors);
                    it = m_pathList.begin();
                    std::advance(it, offset + 1);
                    m_ancestorsTable[clsName] = &(*it);
                }
            }
        }
    }
    if (semant_debug){
        dump_ancestors_map();
    }
    return true;
}

Symbol ClassTable::get_lub(Symbol type1, Symbol type2){
    if ( (m_ancestorsTable.find(type1) == m_ancestorsTable.end()) || (m_ancestorsTable.find(type2) 
                == m_ancestorsTable.end())){
        semant_error() << "Unknow type = " << type1 << endl;
        return Object;
    }

    ClassNameList anc1 = *(m_ancestorsTable[type1]);
    ClassNameList anc2 = *(m_ancestorsTable[type2]);
    
    if (semant_debug){
        cout << "get_lub: ancestors for " << type1 << " -";
        for (ClassNameList::iterator it = anc1.begin(), itEnd = anc1.end();
                it != itEnd; ++it){
            cout << (*it) << ",";
        }
        cout << endl;

        cout << "get_lub: ancestors for " << type2 << " -";
        for (ClassNameList::iterator it = anc2.begin(), itEnd = anc2.end();
                it != itEnd; ++it){
            cout << (*it) << ",";
        }
        cout << endl;
    }

    for(ClassNameList::iterator it1 = anc1.begin(), it1End = anc1.end();
            it1 != it1End; ++it1){
        if (std::count(anc2.begin(), anc2.end(), *it1) != 0){
            return *it1;
        }
    }
    return Object;
}

bool ClassTable::isSuperTypeOf(Symbol type1, Symbol type2){
    if (m_ancestorsTable.find(type2) != m_ancestorsTable.end()){
        ClassNameList& ancestors = *(m_ancestorsTable[type2]);
        return std::count(ancestors.begin(), ancestors.end(), type1) == 1;
    }
    return false;
}

bool ClassTable::check_types(){
    return check_feature_declarations() && check_feature_overrides() \
        && check_feature_implementations();
}

bool ClassTable::check_feature_declarations(){
    bool ret = true;
    //traverse the ASTs and check types
    for (int i = m_classList->first(); m_classList->more(i); i = m_classList->next(i)){
        class__class* cls = dynamic_cast<class__class*>(m_classList->nth(i));
        if (!cls){
            return false;
        }

        m_symTable.enterscope();
        m_symTable.addid(self, &SELF_TYPE);
        m_symTable.addid(SELF_TYPE, new Symbol(cls->get_name()));
        Features features = cls->get_features();
        
        //check method return types and param types first since they may be referenced in attributes
        for (int j = features->first(); features->more(j);  j = features->next(j)){
            Feature feature = features->nth(j);
            if (feature->collect_type(m_symTable, cls->get_name())){
                if (semant_debug)
                    cout << "@@ Method return type checked for " << cls->get_name() << ":" << feature->get_name()
                        << " is done" << endl;
            }else{
                semant_error(cls) << endl;
                ret = false;
            }
        }
        m_symTable.exitscope();

        if (semant_debug){
            cout << "All method declarations for class " << cls->get_name() << " CHECKED!" << endl << endl;
            cout << "-----------------------------" << endl;
        }
    }
    return ret;
}


bool ClassTable::check_feature_overrides(){
    //scan the ancestors map and feature types table
    for (AncestorsMap::iterator it = m_ancestorsTable.begin(), itEnd = m_ancestorsTable.end();
            it != itEnd; ++it){

        Symbol clsName = it->first;
        SymbolList attrs; 
        SymbolList methods; 
        for (FeatureTypesMap::iterator it1 = m_featureTypeTable.begin(), it1End = m_featureTypeTable.end();
                it1 != it1End; ++it1){
            if (it1->first.first == clsName){
                SymbolList& list = (it1->second.second) ? methods : attrs;
                list.push_back(it1->first.second);
            }
        }

        ClassNameList* ancestors = it->second;
        for (ClassNameList::iterator it1 = ancestors->begin(), it1End = ancestors->end();
                it1 != it1End; ++it1){
            if (clsName == *it1){
                continue; //actually always the first node
            }else{
                //Disallow attribute override
                for (SymbolList::iterator it2 = attrs.begin(), it2End = attrs.end();
                        it2 != it2End; ++it2){
                    if (m_featureTypeTable.find(std::make_pair(*it1, *it2)) 
                            != m_featureTypeTable.end()){
                        //attribute redefinition is not allowd!
                        if (semant_debug){
                            cout << "attr redefined!" << endl;
                            return false;
                        }
                        semant_error(find_class_by_name(clsName)) << endl;
                    }
                }
                
                //Check method override types
                for (SymbolList::iterator it2 = methods.begin(), it2End = methods.end();
                        it2 != it2End; ++it2){
                    if (m_featureTypeTable.find(std::make_pair(*it1, *it2)) 
                            != m_featureTypeTable.end()){
                        //all the types must match
                        ParamTypeList typesParent = m_featureTypeTable[std::make_pair(*it1, *it2)].first;
                        ParamTypeList typesOwn    = m_featureTypeTable[std::make_pair(clsName, *it2)].first;
                        if (typesParent.size() != typesOwn.size()){
                            DBGLINE
                            semant_error(find_class_by_name(clsName)) << endl;
                            return false;
                        }else{
                            if (!std::equal(typesOwn.begin(), typesOwn.end(), typesParent.begin())){
                                DBGLINE;
                                semant_error(find_class_by_name(clsName)) << endl;
                                return false;
                            }
                        }
                    }
                }
            }
        }
    }
    return true;
}



bool ClassTable::check_feature_implementations(){
    //traverse the ASTs and check types
    for (int i = m_classList->first(); m_classList->more(i); i = m_classList->next(i)){
        class__class* cls = dynamic_cast<class__class*>(m_classList->nth(i));
        if (!cls){
            return false;
        }

        m_symTable.enterscope();
        m_symTable.addid(self, &SELF_TYPE);
        m_symTable.addid(SELF_TYPE, new Symbol(cls->get_name()));
        Features features = cls->get_features();
        
        //check attributes first to find defined attributes
        for (int j = features->first(); features->more(j);  j = features->next(j)){
            Feature feature = features->nth(j);
            attr_class* attr = dynamic_cast<attr_class*>(feature);
            if (attr && !(attr->check_types(m_symTable))){
                semant_error(cls) << endl;
            }
        }

        //Now check method implementations
        if ((cls->get_name() == Int) || (cls->get_name() == Bool) || (cls->get_name() == Str)
                || (cls->get_name() == IO) || (cls->get_name() == Object)){
            //don't check basic classes
        }else{
            //DO method check on user defined classes
            for (int j = features->first(); features->more(j);  j = features->next(j)){
                Feature feature = features->nth(j);
                method_class* method = dynamic_cast<method_class*>(feature);
                if (semant_debug){
                    cout << "Do method type check on " << cls->get_name() << "::" << feature->get_name() << endl;
                }
                if (method){
                    if (!method->check_types(m_symTable)){
                        //Method type check error
                        semant_error(cls) << endl; 
                        //<< "Method Type check error for " << cls->get_name() << "::" << method->get_name() ;
                    }
                }
            }
        }

        m_symTable.exitscope();

        if (semant_debug)
            cout << "Attrs and methods implementation for class " << cls->get_name() << " done" << endl;
    }
    return true;
}


bool ClassTable::is_inherited_feature(Symbol cls, Symbol method, Symbol& parent, bool isMethod){
    if (m_ancestorsTable.find(cls) == m_ancestorsTable.end()){
        if (semant_debug){
            cout << "Ancestors for " << cls << " not built yet!" << endl;
        }
        return false;
    }
    ClassNameList* ancestors = m_ancestorsTable[cls];
    if (!ancestors){
        if (semant_debug){
            cout << "Ancestors for " << cls << " is NULL!" << endl;
        }
        return false;
    }else{
        for (ClassNameList::iterator it = ancestors->begin(), itEnd = ancestors->end();
                it != itEnd; ++it){
            FeatureTypesMap::iterator itTypeMap = m_featureTypeTable.find(\
                    std::make_pair(*it, method));
            if ( (itTypeMap != m_featureTypeTable.end()) && (itTypeMap->second.second == isMethod)){
                parent = *it;
            }
        }
    }
    return true;
}


void ClassTable::dump_ancestors_map(){
    const char* preamble = "#### ";
    for (AncestorsMap::iterator it = m_ancestorsTable.begin(), itEnd = m_ancestorsTable.end();
            it != itEnd; ++it){
        cout << preamble << setw(12) << it->first << " : ";
        ClassNameList parents = *(it->second);
        for (ClassNameList::iterator it1 = parents.begin(), it1End = parents.end();
                it1 != it1End; ++it1){
            cout << setw(8) << *it1 << "->";
        }
        cout << "ENDMARKER" << endl;
    }
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
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
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
    clsTablePtr = classtable;

    /* some semantic analysis code may go here */
    if (semant_debug)
        cout << "beginning to do check..." << endl;
    classtable->do_check();

    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    }
}

////////////////////////////////////////////////////////////////////////////////
//cool-tree definitions
bool assign_class::check_types(SymTable& symTable){
    bool ret = true;
    Symbol* type = symTable.lookup(name);
    Symbol objType;

    if (type == NULL){
        Symbol parent;
        if (clsTablePtr->is_inherited_feature(*symTable.lookup(SELF_TYPE), name, 
                parent, false)){
            ParamTypeList types = clsTablePtr->get_param_types(parent, name);
            if (types.size() > 0){
                objType = types[types.size() - 1];
            }else{
                DBGLINE
                ret = false;
            }
        }else{
            DBGLINE
            ret = false;
        }
    }else{
        objType = *type;
    }

    if (ret && (expr->check_types(symTable))){
        Symbol expType = expr->get_type();
        if (clsTablePtr->isSuperTypeOf(objType, expType)){
            set_type(expr->get_type());
            return true;
        }else{
            set_type(Object);
            if (semant_debug){
                cout << "Object type:" << objType << " is not super type of " << expType << endl;
            }
            DBGLINE
            return false;
        }
    }
    DBGLINE
    return false;
}

bool static_dispatch_class::check_types(SymTable& symTable){
    bool ret = expr->check_types(symTable);
    if (ret){
        Symbol t0 = expr->get_type();
        ret = ret && clsTablePtr->isSuperTypeOf(type_name, t0);

        //Return type check depends on formal return type of type_name::name
        // If it's SELF_TYPE, set return type as expr's type
        //  Otherwise, using the formal return type
        ParamTypeList typeList = clsTablePtr->get_param_types(type_name, name);
        if (typeList.size() == 0){
            if (semant_debug)
                cout << "$$$ static_dispatch: No types found for " << type_name << ":" << name << endl;
            set_type(Object);
            DBGLINE
            return false;
        }else{
            Symbol retType = typeList[typeList.size() -1];
            set_type(retType == SELF_TYPE ? t0 : retType);
        }

        //check all actual parameter types against formal params
        size_t j = 0;
        bool actTypeChecked = false;
        for (int i = actual->first(); actual->more(i); i = actual->next(i)){
            actTypeChecked = actual->nth(i)->check_types(symTable);
            Symbol curType;
            if ((j < typeList.size() - 1) && actTypeChecked){
                curType = actual->nth(i)->get_type();
                if (curType == SELF_TYPE){
                    curType = *(symTable.lookup(SELF_TYPE));
                }
                if (clsTablePtr->isSuperTypeOf(typeList[j++], curType)){
                    //fine
                }else{
                    if (semant_debug){
                        cout << "Invalid type for parameter " << j << " as type:" << curType << endl;
                    }
                    DBGLINE
                    ret = false;
                }
            }else{
                DBGLINE
                ret = false;
            }
            ret = ret && actTypeChecked;
        }
    }else{
        DBGLINE
        return false;
    }
    
    return ret;
}

bool dispatch_class::check_types(SymTable& symTable){
    bool ret = expr->check_types(symTable);
    Symbol t0 = ret ? expr->get_type() : Object;
    Symbol objType = t0;
    if (t0 == SELF_TYPE){
        objType = *(symTable.lookup(SELF_TYPE));
    }

    //Checking the actual class method signatures
    ParamTypeList typeList = clsTablePtr->get_param_types(objType, name);
    if (typeList.size() == 0){
        if (semant_debug)
            cout << "No types found for " << objType << ":" << name << endl;
        set_type(Object);
        DBGLINE
        return false;
    }

    Symbol retType = typeList[typeList.size() -1];
    if (!retType){
        DBGLINE
        ret = false;
        if (semant_debug)
            cout << "return type is not collected yet for " << t0 << ":" << name << endl;
        set_type(No_type);
    }else{
        set_type(retType == SELF_TYPE ? t0 : retType);
    }

    //check all actual parameter types against formal params
    size_t j = 0;
    bool actTypeChecked = false;
    for (int i = actual->first(); actual->more(i); i = actual->next(i)){
        actTypeChecked = actual->nth(i)->check_types(symTable);
        Symbol curType;
        if ((j < typeList.size() - 1) && actTypeChecked){
            curType = actual->nth(i)->get_type();
            if (curType == SELF_TYPE){
                curType = *(symTable.lookup(SELF_TYPE));
            }
            if (clsTablePtr->isSuperTypeOf(typeList[j++], curType)){
                //fine
            }else{
                if (semant_debug){
                    cout << "Invalid type for parameter " << j << " as type:" << curType << endl;
                }
                DBGLINE
                ret = false;
            }
        }else{
            DBGLINE
            ret = false;
        }
        ret = ret && actTypeChecked;
    }
    if (!ret && semant_debug){
        cout << name << " type check failed for object bound / actual parameters" << endl;
    }
    return ret;
}

bool cond_class::check_types(SymTable& symTable){
    bool ret = true;
    ret = ret && (pred->check_types(symTable));
    if (!ret) DBGLINE
    if ( ret && pred->get_type() == Bool){
        ret = ret && then_exp->check_types(symTable);
        ret = ret && else_exp->check_types(symTable);
        Symbol t1 = then_exp->get_type();
        Symbol t2 = else_exp->get_type();
        Symbol selfType = *(symTable.lookup(SELF_TYPE));
        t1 = ((t1 == SELF_TYPE) ? selfType : t1);
        t2 = ((t2 == SELF_TYPE) ? selfType : t2);
        if (t1 != t2){
            set_type(clsTablePtr->get_lub(t1, t2));
        }else{
            set_type(t1);
        }
        if (semant_debug){
            cout << "cond - then type:" << t1 << ", else type:" << t2
                << ", cond type:" << get_type() << endl;
        }
    }else{
        set_type(Object);
    }
    
    return ret;
}

bool loop_class::check_types(SymTable& symTable){
    set_type(Object);
    if (! (pred->check_types(symTable))){
        DBGLINE;
        return false;
    }

    if (pred->get_type() != Bool){
        if (semant_debug)
            cout << " !!! loop predication is not bool, type = " << (pred->get_type()\
                    ? pred->get_type() : No_type) << endl;
        return false;
    }

    if (!(body->check_types(symTable))){
        DBGLINE
        return false;
    }
    return true;
}

bool typcase_class::check_types(SymTable& symTable){
    bool ret = expr->check_types(symTable);
    bool branchCheck = true;
    ClassNameList typeList;
    ClassNameList declTypeList;

    for (int i = cases->first(); cases->more(i); i = cases->next(i)){
        branchCheck = (cases->nth(i)->check_types(symTable));
        ret = ret && branchCheck;

        //decltype can't be duplicated
        Symbol declType = cases->nth(i)->get_decltype();
        Symbol retType = cases->nth(i)->get_type();
        if (semant_debug){
            cout << "$$$ branch decl type:" << declType << ", ret: " << retType << endl;
        }
        if (std::find(declTypeList.begin(), declTypeList.end(), declType) 
                == declTypeList.end()){
            declTypeList.push_back(declType);
            if (branchCheck){
                typeList.push_back(retType);
            }else{
                DBGLINE
                ret = false;
            }
        }else{
            if (semant_debug)
                cout << "!!! Duplicated case type " << declType << " found in case branches"
                     << " in class " << *(symTable.lookup(SELF_TYPE)) << endl;
            ret = false;
        }
    }

    if (typeList.empty()){
        if (semant_debug){
            cout << "No case statement type collected!" << endl;
        }
        set_type(Object);
    }else{
        //return lub of all the cases types
        if (typeList.size() == 1){
            set_type(typeList[0]);
        }else{
            Symbol lub_type = typeList[0];
            ClassNameList::iterator it = typeList.begin() + 1;
            for (ClassNameList::iterator itEnd = typeList.end(); it != itEnd; ++it){
                Symbol clsType = *(symTable.lookup(SELF_TYPE));
                if (lub_type == SELF_TYPE){
                    lub_type = clsType;
                }
                if (lub_type == (*it)){
                    continue;
                }
                lub_type = clsTablePtr->get_lub(lub_type, (*it) == SELF_TYPE ? clsType : (*it) );
            }
            set_type(lub_type);
        }
    }
    return ret;
}


bool branch_class::check_types(SymTable& symTable){
    symTable.enterscope();
    symTable.addid(name, &type_decl);
    bool ret = expr->check_types(symTable);   
    symTable.exitscope();

    set_type(ret ? expr->get_type() : Object);
    return ret;
}


bool block_class::check_types(SymTable& symTable){
    bool ret = true;
    for (int i = body->first(); body->more(i); i = body->next(i)){
        if (!(body->nth(i)->check_types(symTable))){
            ret = false;
            DBGLINE
        }
    }
    set_type(body->nth(body->len() - 1)->get_type());
    return ret;
}


bool let_class::check_types(SymTable& symTable){
    init->check_types(symTable);
    bool ret = true;

    //check identifier type
    if (identifier == self){
        DBGLINE
        ret = false;
    }

    //init type checking shall conform to identifier type
    Symbol initType = init->get_type();
    if (initType != No_type){
        Symbol identifierType = type_decl;
        if (type_decl == SELF_TYPE){
            identifierType = *symTable.lookup(SELF_TYPE);
        }

        if (initType == SELF_TYPE){
            initType = *symTable.lookup(SELF_TYPE);
        }
        if (!(clsTablePtr->isSuperTypeOf(identifierType, initType))){
            DBGLINE
            ret = false;
        }
    }

    symTable.enterscope();
    symTable.addid(identifier, &type_decl);
    if (!(body->check_types(symTable))){
        DBGLINE
        ret = false;
    }

    symTable.exitscope();
    set_type(body->get_type());
    //cout << "let type is:" << body->get_type() << endl;
    return ret;
}


bool plus_class::check_types(SymTable& symTable){
    bool ret = e1->check_types(symTable);
    ret = ret && e2->check_types(symTable);
    if ( (e1->get_type() != Int) || (e2->get_type() != Int)){
        set_type(Int);
        return false;
    }else{
        set_type(Int);
    }
    return ret;
}

bool sub_class::check_types(SymTable& symTable){
    bool ret = e1->check_types(symTable);
    ret = ret && e2->check_types(symTable);
    if ( (e1->get_type() != Int) || (e2->get_type() != Int)){
        set_type(Int);
        DBGLINE
        return false;
    }else{
        set_type(Int);
    }
    return ret;
}

bool mul_class::check_types(SymTable& symTable){
    bool ret = e1->check_types(symTable);
    ret = ret && e2->check_types(symTable);
    if ( (e1->get_type() != Int) || (e2->get_type() != Int)){
        set_type(Int);
        return false;
    }else{
        set_type(Int);
    }
    return ret;
}

bool divide_class::check_types(SymTable& symTable){
    bool ret = e1->check_types(symTable);
    ret = ret && e2->check_types(symTable);
    if ( (e1->get_type() != Int) || (e2->get_type() != Int)){
        set_type(Int);
        return false;
    }else{
        set_type(Int);
    }
    return ret;
}

bool neg_class::check_types(SymTable& symTable){
    if ((e1->check_types(symTable)) && e1->get_type() && (e1->get_type() != Int)){
        if (semant_debug){
            cout << "Assigning type " << e1->get_type() << " to Int" << endl;
        }
        set_type(Object);
        return false;
    }else{
        set_type(Int);
    }
    return true;
}

bool lt_class::check_types(SymTable& symTable){
    bool ret = e1->check_types(symTable);
    if (!ret) DBGLINE
    ret = e2->check_types(symTable) && ret;
    if (!ret) DBGLINE
    set_type(Bool);

    if ( (e1->get_type() != Int) || (e2->get_type() != Int)){
        DBGLINE
        return false;
    }
    return ret;
}

bool eq_class::check_types(SymTable& symTable){
    bool ret = e1->check_types(symTable);
    ret = ret && e2->check_types(symTable);
    set_type(Bool);

    if (((e1->get_type() == Int) || (e1->get_type() == Bool) || (e1->get_type() == Bool) 
            || (e2->get_type() == Int) || (e2->get_type() == Bool) || (e2->get_type() == Bool))){
            ret = ret && (e1->get_type() == e2->get_type());
    }else{
        return ret;
    }
    if (!ret) DBGLINE
    //cout << "equal check returns " << ret << endl;
    return ret;
}

bool leq_class::check_types(SymTable& symTable){
    DBGLINE
    bool ret = e1->check_types(symTable);
    ret = ret && e2->check_types(symTable);
    set_type(Bool);

    if ( (e1->get_type() != Int) || (e2->get_type() != Int))
        return false;
    return ret;
}

bool comp_class::check_types(SymTable& symTable){
    bool ret = e1->check_types(symTable);
    set_type(e1->get_type());
    return ret;
}

bool int_const_class::check_types(SymTable& symTable){
    set_type(Int);
    return true;
}

bool bool_const_class::check_types(SymTable& symTable){
    set_type(Bool);
    return true;
}

bool string_const_class::check_types(SymTable& symTable){
    set_type(Str);
    return true;
}

bool new__class::check_types(SymTable& symTable){
    //set_type((type_name == SELF_TYPE) ? *(symTable.lookup(SELF_TYPE)) : type_name);
    set_type(type_name);
    return true;
}

bool isvoid_class::check_types(SymTable& symTable){
    set_type(Bool);
    if (! (e1->check_types(symTable))){
        return false;
    }
    return true;
}

bool no_expr_class::check_types(SymTable& symTable){
    set_type(No_type);
    return true;
}

bool object_class::check_types(SymTable& symTable){
    Symbol* sym =  symTable.lookup(name);
    if (sym){
        set_type(*sym);
    }else{
        //check if it's defined in parent attribute list
        Symbol parent;
        if (clsTablePtr->is_inherited_feature(*symTable.lookup(SELF_TYPE), name, 
                parent, false)){
            ParamTypeList types = clsTablePtr->get_param_types(parent, name);
            if (types.size() > 0){
                set_type(types[types.size() - 1]);
                return true;
            }else{
                set_type(Object);
                DBGLINE
                return false;
            }
        }else{
            DBGLINE
            return false;
        }
    }
    return true;
}

bool method_class::collect_type(SymTable& table, Symbol clsName){
    //save formal types
    ClassNameList nameList;
    for (int i = formals->first(); formals->more(i); i = formals->next(i)){
        Symbol type = formals->nth(i)->get_type();
        if (type == SELF_TYPE){
            if (semant_debug)
                cout << "SELF_TYPE in formal name in " << clsName << ":" << name << endl;
            return false;
        }

        Symbol curName = formals->nth(i)->get_name();
        if (curName == self){
            if (semant_debug)
                cout << "Self in formal name in " << clsName << ":" << name << endl;
            return false;
        }
        else if (std::find(nameList.begin(), nameList.end(), curName) == nameList.end()){
            clsTablePtr->collect_param_type(clsName, name, type);
            nameList.push_back(curName);
        }else{
            if (semant_debug)
                cout << "Duplicated formal name " << curName << " in " << clsName << ":" << name << endl;
            return false;
        }
    }
    //if (semant_debug)
    //    cout << "@@@@ return type for " << clsName << ":" << name 
    //        << " is " << return_type << endl;
    clsTablePtr->collect_param_type(clsName, name, return_type);
    return true;
}


bool method_class::check_types(SymTable& symTable){
    symTable.enterscope();
    //bind formal parameters into scope
    for (int i = formals->first(); formals->more(i); i = formals->next(i)){
        symTable.addid(formals->nth(i)->get_name(), new Symbol(formals->nth(i)->get_type()));
    }
    bool ret = expr->check_types(symTable);
    symTable.exitscope();
    if (!ret && semant_debug){
        cout << "****** Errors found in method body of - " << *(symTable.lookup(SELF_TYPE)) 
             << ":" << name << endl;
    }else{
        Symbol actType = expr->get_type();
        //cout << "Act return type = " << actType << endl;
        if (actType == No_type){
            ret = false;
        }else if(actType == SELF_TYPE){
            actType = *(symTable.lookup(SELF_TYPE));
        }
        else if (!(clsTablePtr->isSuperTypeOf(return_type, actType))){
            if (semant_debug){
                cout << "Method " << name << " Actual return type " << actType << " is not sub type of " 
                    << return_type << endl;
            }
            ret = false;
        }
    }
    return ret;
}

bool attr_class::collect_type(SymTable& table, Symbol clsName){
    clsTablePtr->collect_param_type(clsName, name, type_decl, false);
    return true;
}


bool attr_class::check_types(SymTable& symTable){
    if (semant_debug)
        cout << "found definition of attr = " << name << endl;
    if (name == self){
        init->check_types(symTable);
        return false;
    }
    symTable.addid(name, &type_decl);
    return init->check_types(symTable);
}

