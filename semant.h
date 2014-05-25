#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>  
#include <vector>  
#include <tr1/unordered_map>  
#include <map>  
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"

#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.


typedef struct ClassVisitInfo{
    Symbol name;
    Symbol parent;
    int    visit;

    ClassVisitInfo():name(0), parent(0), visit(0) {}
    ClassVisitInfo(const ClassVisitInfo& ref) : name(ref.name), parent(ref.parent), visit(ref.visit){}
    ClassVisitInfo& operator= (const ClassVisitInfo& ref){
        if (&ref != this){
            name = ref.name;
            parent = ref.parent;
            visit = ref.visit;
        }
        return *this;
    }
}ClassVisitInfo;

typedef std::vector<ClassVisitInfo> ClassVisitList;
typedef ClassVisitList::iterator VisitIt;
typedef ClassVisitList::const_iterator VisitCIt;

typedef std::vector<Symbol> ClassNameList;
typedef ClassNameList SymbolList;
typedef std::vector<ClassNameList> AncestorsPathList;
typedef std::tr1::unordered_map<Symbol, ClassNameList*> AncestorsMap;

typedef ClassNameList ParamTypeList;
typedef std::pair<ParamTypeList, bool> FeatureTypesValue;
typedef std::pair<Symbol, Symbol> DeclKey; //key as <clsName, method_name>
typedef std::map<DeclKey, FeatureTypesValue> FeatureTypesMap;

typedef SymbolTable<Symbol, Symbol> SymTable;

class ClassTable {
private:
  int semant_errors;
  void install_basic_classes();
  ostream& error_stream;

  ClassVisitList    m_visitGraph;
  Classes           m_classList;
  ClassNameList     m_classNameList;
  AncestorsPathList m_pathList; 
  AncestorsMap      m_ancestorsTable;
  FeatureTypesMap   m_featureTypeTable;
  SymTable          m_symTable;

  //check for inheritance graph
  bool check_class_relations();
  bool check_types();

  bool check_feature_declarations();
  bool check_feature_overrides();
  bool check_feature_implementations();

  //get class by name
  Class_ find_class_by_name(Symbol name);

  //dump
  void dump_ancestors_map();

public:
  ClassTable(Classes);

  bool do_check();

  //check and get least upper bound type
  Symbol get_lub(Symbol type1, Symbol type2);
  bool isSuperTypeOf(Symbol type1, Symbol type2);

  //collect formals
  void collect_param_type(Symbol cls, Symbol method, Symbol type, bool isMethod = true){
      m_featureTypeTable[std::make_pair(cls, method)].first.push_back(type);
      m_featureTypeTable[std::make_pair(cls, method)].second = isMethod;
  }

  ParamTypeList get_param_types(Symbol cls, Symbol method){
      if (m_featureTypeTable.find(std::make_pair(cls, method)) != m_featureTypeTable.end()){
          return m_featureTypeTable[std::make_pair(cls, method)].first;
      }else{
          //check for ancestors
          Symbol parent;
          if (is_inherited_feature(cls, method, parent)){
              return m_featureTypeTable[std::make_pair(parent, method)].first;
          }else{
              return ParamTypeList();
          }
      }
  }

  bool is_inherited_feature(Symbol cls, Symbol name, Symbol& parent, bool isMethod = true);

  int errors() { return semant_errors; }
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);
};

#endif

