#ifndef spicyQueso_HEADER
#define spicyQueso_HEADER

#include "queso.h"
#include "graph/quesoGraph.h"
#include <algorithm>
#include <inttypes.h>
#include <list>
#include <map>
#include <numeric>
#include <set>
#include <sstream>


enum ShadowState {
    TRUE,
    FALSE,
    IFF
};

class OperandShadow : public Variable {
    private :
        ShadowState shadowState;
        Variable * iffVariable;
    public :
        OperandShadow (const std::string & name, ShadowState shadowState)
            : Variable (1, name), shadowState (shadowState), iffVariable (NULL) {}

        OperandShadow (const std::string & name, ShadowState shadowState, const Variable * iffVariable)
            : Variable (1, name), shadowState (shadowState), iffVariable (iffVariable->copy()) {}

        ~OperandShadow () {
            if (iffVariable != NULL)
                delete iffVariable;
        }

        OperandShadow * copy () const {
            if (iffVariable == NULL)
                return new OperandShadow(g_name(), shadowState);
            else
                return new OperandShadow(g_name(), shadowState, iffVariable);
        }

        std::string smtlib2 () const {
            return Variable::smtlib2();
        }

        std::string shadowSmtlib2 () const {
            if (shadowState == TRUE)
                return Variable::smtlib2();
            else if (shadowState == FALSE)
                return std::string("(bvnot ") + Variable::smtlib2() + ")";
            else if (shadowState == IFF) {
                std::stringstream ss;
                ss << "(ite (= " << Variable::smtlib2() << " #b1) " << iffVariable->smtlib2() << " #b0)";
                return ss.str();
            }
        }

        ShadowState g_shadowState () const { return shadowState; }

        std::string queso () const {
            if (shadowState == FALSE)
                return std::string("~(") + Variable::queso() + ")";
            else if (shadowState == IFF)
                return std::string("IFF(") + Variable::queso() + ")";
            else
                return Variable::queso();
        }
};



class InstructionShadow : public Instruction {
    private :
        std::set <std::set<OperandShadow *>> exclusiveConjunctions;
        Variable * dst;

    public :
        InstructionShadow (const Variable * dst)
            : Instruction () {
            this->dst = dst->copy();
        }

        ~InstructionShadow () {
            std::set <std::set <OperandShadow *>> :: iterator it;
            for (it = exclusiveConjunctions.begin(); it != exclusiveConjunctions.end(); it++) {
                std::set <OperandShadow *> :: iterator iit;
                for (iit = (*it).begin(); iit != (*it).end(); iit++) {
                    delete *iit;
                }
            }
            delete dst;
        }

        void addConjunction (std::set <OperandShadow *> conjunction) {
            exclusiveConjunctions.insert(conjunction);
        }

        const Variable * g_dst () const { return dst; }

        void s_dst (const Variable * dst) {
            delete this->dst;
            this->dst = dst->copy();
        }

        Operand * operand_written () { return dst; }

        std::list <Operand *> operands_read () {
            std::list <Operand *> operands_read;

            std::set <std::set<OperandShadow *>> :: iterator it;
            for (it = exclusiveConjunctions.begin(); it != exclusiveConjunctions.end(); it++) {
                std::set <OperandShadow *> ::iterator iit;
                for (iit = (*it).begin(); iit != (*it).end(); iit++) {
                    operands_read.push_back(*iit);
                }
            }

            return operands_read;
        }

        std::list <Operand *> operands () {
            std::list <Operand *> operands = operands_read();
            operands.push_back(dst);
            return operands;
        }

        const std::string smtlib2 () const {
            if (exclusiveConjunctions.size() < 1)
                return "";

            std::stringstream ss;

            ss << "(assert (= " << dst->smtlib2() << " ";

            std::list <std::string> conjunctions;
            std::set <std::set <OperandShadow *>> :: iterator it;
            for (it = exclusiveConjunctions.begin(); it != exclusiveConjunctions.end(); it++) {
                if ((*it).size() == 1) {
                    conjunctions.push_back((*(*it).begin())->shadowSmtlib2());
                    continue;
                }

                std::list <std::string> conjunctionStrings;
                for (auto iit = (*it).begin(); iit != (*it).end(); iit++) {
                    conjunctionStrings.push_back((*iit)->shadowSmtlib2());
                }

                conjunctions.push_back(std::accumulate(conjunctionStrings.begin(),
                                                       conjunctionStrings.end(),
                                                       std::string(""),
                    [] (std::string a, std::string b) {
                        if (a == "") return b;
                        std::stringstream ss;
                        ss << "(bvand " << a << " " << b << ")";
                        return ss.str();
                    }));
            }

            if (conjunctions.size() == 1)
                ss << conjunctions.front();
            else {
                ss << std::accumulate(conjunctions.begin(), conjunctions.end(), std::string(""),
                    [] (std::string a, std::string b) {
                        if (a == "") return b;
                        std::stringstream ss;
                        ss << "(bvxor " << a << " " << b << ")";
                        return ss.str();
                    });
            }

            ss << "))";
            return ss.str();
        }

        const std::string queso () const {
            std::stringstream result;

            result << "shadowInstruction " << dst->queso() << " = ";

            std::list <std::string> conjunctions;
            std::set <std::set <OperandShadow *>> :: iterator it;
            for (it = exclusiveConjunctions.begin(); it != exclusiveConjunctions.end(); it++) {
                std::list <std::string> conjunctionStrings;
                for (auto iit = (*it).begin(); iit != (*it).end(); iit++)
                    conjunctionStrings.push_back((*iit)->queso());
                conjunctions.push_back(
                    std::string("{") + std::accumulate(conjunctionStrings.begin(),
                                                       conjunctionStrings.end(),
                                                       std::string(""),
                        [] (std::string lhs, std::string rhs) {
                            if (lhs == "") return rhs;
                            return lhs + std::string(" & ") + rhs;
                        })
                    + std::string("}"));
            }
            result << std::accumulate(conjunctions.begin(),
                                      conjunctions.end(),
                                      std::string(""),
                [] (std::string lhs, std::string rhs) {
                    if (lhs == "") return rhs;
                    return lhs + " \\n^ " + rhs;
                });
            return result.str();
        }

        InstructionShadow * copy  () const {
            InstructionShadow * newIns = new InstructionShadow(dst);
            std::set <std::set <OperandShadow *>> :: const_iterator it;
            for (it = exclusiveConjunctions.begin(); it != exclusiveConjunctions.end(); it++) {
                std::set <OperandShadow *> shadowCopy;
                std::set <OperandShadow *> :: iterator iit;
                for (iit = (*it).begin(); iit != (*it).end(); iit++) {
                    shadowCopy.insert((*iit)->copy());
                }
                newIns->addConjunction(shadowCopy);
            }
            return newIns;
        }
};


class LiveVertex : public GraphVertex {
    private :
        std::list <Operand *> variables_in;
        std::list <Operand *> variables_out;
    public :
        void variable_in (Operand * operand);
        void variable_out (Operand * operand);
};


class SpicyQueso {
    public :

        // apply ssa over a single instruction
        static void ssa_instruction (Instruction * instruction);

        /* Looks for instructions that assign to needle. Replaces
         * that instruction with an assignment of value to needle.
         */
        static bool replace_with_assign (Instruction * instruction,
                                         const Variable * needle,
                                         const Operand * value);

        /* Looks for instructions that assign to needle. Replaces
         * that instruction with given instruction.
         */
        static bool replace_with_instruction (Instruction * instruction,
                                              const Operand * needle,
                                              const Instruction * newInstruction);

        /* Replace operand in a single instruction.
         * Returns false if operand replaced, false otherwise.
         * If true, newOperand is copied.
         */
        static bool replace_operand_instruction (Instruction * instruction,
                                                 const std::string & needle,
                                                 const Operand * newOperand);

        static void ssa2 (QuesoGraph * quesoGraph);

        static void blockize   (QuesoGraph * quesoGraph);

        /* REQUIRES ACYCLIC GRAPH
         * finds all variables (Variable and Array) that are live at the point
         * of all exit vertices in the graph, where exit vertices are vertices
         * with no successors
         * the result is a string of operand->queso() that can be used to
         * quickly check if a given variable is live
         */
        static std::set <std::string> find_live_variables (QuesoGraph * quesoGraph);

        static void dead_code_elimination (QuesoGraph * quesoGraph);
        static void constant_fold_propagate (QuesoGraph * quesoGraph);

        static void replace_operand (QuesoGraph * quesoGraph,
                                     const Operand * needle,
                                     const Operand * newOperand);

        // returns a map of dominators for every vertex in the graph
        static std::map <uint64_t, std::set <uint64_t>> dominator_map (QuesoGraph * quesoGraph);

        // returns a map of predecessors for every vertex in the graph
        static std::map <uint64_t, std::set <uint64_t>> predecessor_map (QuesoGraph * quesoGraph);

        static std::map <uint64_t, uint64_t> idominator_map (QuesoGraph * quesoGraph,
                                  std::map <uint64_t, std::set <uint64_t>> & dom_map);

        static QuesoGraph * shadowGraph  (QuesoGraph * quesoGraph);
        static QuesoGraph * shadowGraph2 (QuesoGraph * quesoGraph);
};

#endif