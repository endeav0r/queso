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


class OperandShadow : public Variable {
    private :
        bool Not;
    public :
        OperandShadow (const std::string & name, bool Not)
            : Variable (1, name), Not (Not) {}

        OperandShadow * copy () const {
            return new OperandShadow(g_name(), Not);
        }

        std::string smtlib2 () const {
            std::stringstream ss;
            if (Not == false) {
                ss << "(not " << Variable::smtlib2() << ")";
                return ss.str();
            }
            else
                return Variable::smtlib2();
        }

        std::string queso () const {
            if (Not == false)
                return std::string("~(") + Variable::queso() + ")";
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
            std::stringstream ss;

            ss << "(assert (= " << dst->smtlib2() << " ";

            std::list <std::string> conjunctions;
            std::set <std::set <OperandShadow *>> :: iterator it;
            for (it = exclusiveConjunctions.begin(); it != exclusiveConjunctions.end(); it++) {
                if ((*it).size() == 1) {
                    conjunctions.push_back((*(*it).begin())->smtlib2());
                    continue;
                }

                std::list <std::string> conjunctionStrings;
                std::transform((*it).begin(),
                               (*it).end(),
                               conjunctionStrings.begin(),
                               [](OperandShadow * opS) { return opS->smtlib2(); });

                conjunctions.push_back(std::accumulate(conjunctionStrings.begin(),
                                                       conjunctionStrings.end(),
                                                       std::string(""),
                    [] (std::string a, std::string b) { 
                        std::stringstream ss;
                        ss << "(and " << a << " " << b << ")";
                        return ss.str();
                    }));
            }

            if (conjunctions.size() == 1)
                ss << conjunctions.front();
            else {
                ss << std::accumulate(conjunctions.begin(), conjunctions.end(), std::string(""),
                    [] (std::string a, std::string b) {
                        std::stringstream ss;
                        ss << "(xor " << a << " " << b << ")";
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
                    return lhs + " ^ " + rhs;
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


class SpicyQueso {
    public :
        static void ssa (std::list <Instruction *> & instructions);
        static void ssa (QuesoGraph * quesoGraph);

        static void ssa2 (QuesoGraph * quesoGraph);

        static void blockize   (QuesoGraph * quesoGraph);
        static void unblockize (QuesoGraph * quesoGraph);

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

        static QuesoGraph * shadowGraph (QuesoGraph * quesoGraph);
};

#endif