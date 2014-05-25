#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>  
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"
#include <vector>

using std::vector;


#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

inline int comp_two_type(Symbol a, Symbol b)
{
    if (a == NULL || b == NULL)
        return false;

    return a->equal_string(b->get_string(), b->get_len());
}


class TreeNode;

class TreeNode {
private:
        Symbol node_name;
        Symbol parent;
        vector<TreeNode *> *sibling;
        TreeNode() {}
public:
        typedef vector<TreeNode *>::iterator VSI;
        Symbol lub(TreeNode *root, Symbol t1, Symbol t2);
        TreeNode(Symbol name, Symbol pparent) {
                node_name = name;
                sibling = new vector<TreeNode *>();
                parent = pparent;
#ifdef DDD                
                cout << "create node: " << name;
                if (parent)
                        cout << " parent : " << parent;
                cout << endl;
#endif
        }
        virtual ~TreeNode() {
#ifdef DDD
                cout <<  "deleting ndoe: " << node_name << endl;
#endif
                delete sibling;
        }

        bool same_name(Symbol a) { return comp_two_type(a, node_name); }

        TreeNode *get(TreeNode *n, Symbol a) {

                if (comp_two_type(n->node_name, a)) {
                        return n;
                }
                for (VSI i = n->sibling->begin();
                     i != n->sibling->end();
                     ++i) {
                        TreeNode *nn = get(*i, a);
                        if (nn != NULL) {
                                return nn;
                        }
                }
                return NULL;
        }

        void dump_sibling() {
                for (VSI i = sibling->begin(); i != sibling->end(); i++)
                        cout << "  sib: " << (*i)->node_name << endl;
                
        }

        void dump_tree() {
                cout << " \t\t " << node_name;
                if (parent)
                        cout << " parent : " << parent;
                cout << "\n";
                for (VSI i = sibling->begin(); i != sibling->end(); i++) {
                        cout << "  sib: " << (*i)->node_name << endl;
                        (*i)->dump_tree();
                }
        }

        bool addchild(Symbol name, Symbol parent) {
                TreeNode *p = get(this, parent);
                if (p == NULL) {
                        return false;
                }
                TreeNode *n = get(this, name);
                if (n != NULL) {
                        return false;
                }
                p->sibling->push_back(new TreeNode(name, parent));
                return true;
        }

        /* Return if class A is a subclass of class B */
        bool isSubClass(Symbol a, Symbol b) {
                TreeNode *n = get(this, b);
                if (n == NULL) {
                        return false;
                }
                TreeNode *n2 = get(n, a);
                return n2 != NULL;
        }


        Symbol get_parent() {
                return parent;
        }

        Symbol get_node_name() {
                return node_name;
        }
};


typedef SymbolTable<Symbol, Entry> ClassSymbolTable;

class ClassTable {
private:
  int semant_errors;
  int pass;
  void install_basic_classes();
  ostream& error_stream;
  Classes _root;
  TreeNode *classTreeRoot;
  typedef Symbol Type;

  /* Symbol table for current method. */
  typedef SymbolTable<Symbol, Entry> MethodSymbolTable;
  MethodSymbolTable *currMethodST;
  
  /* Symbol table for each of classes. */

  /* Symbol table for the global classes. */
  typedef SymbolTable<Symbol, ClassSymbolTable> GlobalSymbolTable;

  GlobalSymbolTable *_globalmap;

public:
  ClassTable(Classes);
  int errors() { return semant_errors; }

  Symbol findSymbolToObject(Symbol node, Symbol method_or_attr);
  bool isInternalClassName(Symbol a);
  bool invalidParentClassName(Symbol a);
  Symbol access_dispatch_and_static(Class_ c,
                                    static_dispatch_class *static_c,
                                    dispatch_class *dis_c, ClassSymbolTable *t);
  Symbol self_type_c(Class_ c);
  Symbol access_expr(Class_ c, Expression_class *e, ClassSymbolTable *t );
  void access_method(Class_ c, method_class *m, ClassSymbolTable *t);
  void access_attr(Class_ c, attr_class *attr, ClassSymbolTable *t);
  void access_features(Class_ c, Features fs, ClassSymbolTable *t);
  void access_tree_node(Classes class_, ClassTable *classtable);
  
  void access_class(tree_node *);
  void first_pass();
  void second_pass();
  
  
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Class_ c, const char *errormsg);
  ostream& semant_error_line(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);
};


#endif

