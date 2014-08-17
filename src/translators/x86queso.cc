#include "x86queso.h"

#include "queso/generic_instructions.h"

#include <iostream>
#include <stdexcept>
#include <sstream>
#include <cstdio>

//#define DEBUG_x86TRANSLATE


InstructionX86 * QuesoX86 :: translate (const uint8_t * data,
                                        size_t size,
                                        uint64_t pc,
                                        bool setpc) {
    if (ix86 != NULL)
        delete ix86;

    ud_init(&ud_obj);
    ud_set_mode(&ud_obj, 32);
    ud_set_syntax(&ud_obj, UD_SYN_INTEL);

    ud_set_input_buffer(&ud_obj, (unsigned char *) data, size);

    if (ud_disassemble(&ud_obj) == 0)
        return NULL;

    #ifdef DEBUG_x86TRANSLATE
    printf("DEBUG_X86TRANSLATE %s\n", ud_insn_asm(&ud_obj));fflush(stdout);
    #endif

    if (setpc)
        ix86 = new InstructionX86(ud_insn_asm(&ud_obj), data, ud_insn_len(&ud_obj), pc);
    else
        ix86 = new InstructionX86(ud_insn_asm(&ud_obj), data, ud_insn_len(&ud_obj));

    ix86->pdi(new InstructionAdd(Variable(32, "eip"),
                                 Variable(32, "eip"),
                                 Constant(32, ud_insn_len(&ud_obj))));

    switch (ud_obj.mnemonic) {
    case UD_Iadd    : add(); break;
    case UD_Iand    : And(); break;
    case UD_Icall   : call(); break;
    case UD_Icmova  : cmova(); break;
    case UD_Icmovb  : cmovb(); break;
    case UD_Icmovbe : cmovbe(); break;
    case UD_Icmovnz : cmovnz(); break;
    case UD_Icmovs  : cmovs(); break;
    case UD_Icmovz  : cmovz(); break;
    case UD_Icmp    : cmp(); break;
    case UD_Icwde   : cwde(); break;
    case UD_Idec    : dec(); break;
    case UD_Iinc    : inc(); break;
    case UD_Ija     : ja(); break;
    case UD_Ijae    : jae(); break;
    case UD_Ijb     : jb(); break;
    case UD_Ijbe    : jbe(); break;
    case UD_Ijg     : jg(); break;
    case UD_Ijl     : jl(); break;
    case UD_Ijle    : jle(); break;
    case UD_Ijmp    : jmp(); break;
    case UD_Ijns    : jns(); break;
    case UD_Ijnz    : jnz(); break;
    case UD_Ijs     : js(); break;
    case UD_Ijz     : jz(); break;
    case UD_Ilea    : lea(); break;
    case UD_Ileave  : leave(); break;
    case UD_Imov    : mov(); break;
    case UD_Imovd   : movd(); break;
    case UD_Imovsd  : movsd(); break;
    case UD_Imovzx  : movzx(); break;
    case UD_Inop    : nop(); break;
    case UD_Inot    : Not(); break;
    case UD_Ior     : Or(); break;
    case UD_Ipop    : pop(); break;
    case UD_Ipush   : push(); break;
    case UD_Iret    : ret(); break;
    case UD_Ishr    : shr(); break;
    case UD_Isub    : sub(); break;
    case UD_Itest   : test(); break;
    case UD_Ixor    : Xor(); break;
    default :
        break;
    }

    return ix86;
}


InstructionX86 * QuesoX86 :: translate (const uint8_t * data, size_t size) {
    return translate(data, size, 0, false);
}


InstructionX86 * QuesoX86 :: translate (const uint8_t * data, size_t size, uint64_t pc) {
    return translate(data, size, pc, true);
}


Variable fullReg (unsigned int reg) {
    switch (reg) {
    case UD_R_AL :
    case UD_R_AH :
    case UD_R_AX :
    case UD_R_EAX :
        return Variable(32, "eax");
    case UD_R_BL :
    case UD_R_BH :
    case UD_R_BX :
    case UD_R_EBX :
        return Variable(32, "ebx");
    case UD_R_CL :
    case UD_R_CH :
    case UD_R_CX :
    case UD_R_ECX :
        return Variable(32, "ecx");
    case UD_R_DL :
    case UD_R_DH :
    case UD_R_DX :
    case UD_R_EDX :
        return Variable(32, "edx");
    case UD_R_ESP :
        return Variable(32, "esp");
    case UD_R_EBP :
        return Variable(32, "ebp");
    case UD_R_ESI :
        return Variable(32, "esi");
    case UD_R_EDI :
        return Variable(32, "edi");
    }
    throw std::runtime_error("invalid register");
}


Variable QuesoX86 :: getRegister (unsigned int reg) {
    switch (reg) {
    case UD_R_AH :
    case UD_R_BH :
    case UD_R_CH :
    case UD_R_DH : {
        Variable rh = 
            (reg == UD_R_AH ? Variable(8, "ah") :
             (reg == UD_R_BH ? Variable(8, "bh") :
              (reg == UD_R_CH ? Variable(8, "ch") :
               (reg == UD_R_DH ? Variable(8, "dh") :
                Variable(0, "error")))));
        Constant eight = Constant(32, 8);
        Variable fullreg = fullReg(reg);
        Variable tmp = Variable(32, "tmpGetRegister");
        ix86->pdi(new InstructionShr(tmp, fullreg, eight));
        ix86->pdi(new InstructionAssign(rh, tmp));
        return rh;
    }
    case UD_R_AL :
    case UD_R_BL :
    case UD_R_CL :
    case UD_R_DL : {
        Variable rl = 
            (reg == UD_R_AL ? Variable(8, "al") :
             (reg == UD_R_BL ? Variable(8, "bl") :
              (reg == UD_R_CL ? Variable(8, "cl") :
               (reg == UD_R_DL ? Variable(8, "dl") :
                Variable(0, "error")))));
        ix86->pdi(new InstructionAssign(rl, fullReg(reg)));
        return rl;
    }
    case UD_R_AX :
    case UD_R_BX :
    case UD_R_CX :
    case UD_R_DX : {
        Variable rx = 
            (reg == UD_R_AX ? Variable(16, "ax") :
             (reg == UD_R_BX ? Variable(16, "bx") :
              (reg == UD_R_CX ? Variable(16, "cx") :
               (reg == UD_R_DX ? Variable(16, "dx") :
                Variable(0, "error")))));
        ix86->pdi(new InstructionAssign(rx, fullReg(reg)));
        return rx;
    }
    case UD_R_EAX :
    case UD_R_EBX :
    case UD_R_ECX :
    case UD_R_EDX :
    case UD_R_ESI :
    case UD_R_EDI :
    case UD_R_ESP :
    case UD_R_EBP :
        return fullReg(reg);
    }

    std::stringstream ss;
    ss << "unknown register... " << reg;
    throw std::runtime_error(ss.str());
}


Constant QuesoX86 :: operand_lval (unsigned int bits, ud_operand operand) {
    switch (bits) {
    case 8  : return Constant(8, operand.lval.ubyte);
    case 16 : return Constant(16, operand.lval.uword);
    case 32 : return Constant(32, operand.lval.udword);
    default :
        throw std::runtime_error("invalid operand_lval offset");
    }
    return Constant(0, 0);
}


Operand * QuesoX86 :: sib (ud_operand operand) {
    Variable base(0, "");
    Variable index(0, "");
    Constant scale(0, 0);
    Constant displ(0, 0);

    if (operand.base)
        base = getRegister(operand.base);
    if (operand.index)
        index = getRegister(operand.index);
    if (operand.scale)
        scale = Constant(index.g_bits(), operand.scale);
    if (operand.offset)
        displ = operand_lval(operand.offset, operand);

    Variable index_scale = index;
    if (operand.index && operand.scale) {
        index_scale = Variable(index_scale.g_bits(), "index_scale");
        ix86->pdi(new InstructionMul(index_scale, index, scale));
    }

    if (operand.base) {
        if (operand.offset) {
            if (operand.index) {
                Variable sib(32, "sib");
                ix86->pdi(new InstructionSignExtend(sib, displ));
                ix86->pdi(new InstructionAdd(sib, sib, index_scale));
                ix86->pdi(new InstructionAdd(sib, sib, base));
                return sib.copy();
            }
            // (operand.base) (operand.offset) (! operand.index)
            else {
                Variable sib(32, "sib");
                ix86->pdi(new InstructionSignExtend(sib, displ));
                ix86->pdi(new InstructionAdd(sib, sib, base));
                return sib.copy();
            }
        }
        else {
            if (operand.index) {
                Variable sib(32, "sib");
                ix86->pdi(new InstructionAdd(sib, base, index_scale));
                return sib.copy();
            }
            else
                return base.copy();
        }
    }
    else {
        if (operand.offset) {
            if (operand.index) {
                Variable sib(32, "sib");
                ix86->pdi(new InstructionAdd(sib, index_scale, displ));
                return sib.copy();
            }
            // (! operand.base) (operand.offset) (! operand.index)
            else
                return displ.copy();
        }
        else
            return index_scale.copy();
    }
}


Operand * QuesoX86 :: operandGet (unsigned int place) {
    struct ud_operand operand = ud_obj.operand[place];

    if (operand.type == UD_OP_REG)
        return getRegister(operand.base).copy();
    else if (operand.type == UD_OP_MEM) {
        Operand * address = sib(operand);
        Variable loaded(operand.size, "loaded");
        Array memory(8, "memory", 32);
        switch (operand.size) {
        case 8  : ix86->pdi(new InstructionLoad(&loaded, &memory, address)); break;
        case 16 : ix86->pdi(new InstructionLoadLE16(&loaded, &memory, address)); break;
        case 32 : ix86->pdi(new InstructionLoadLE32(&loaded, &memory, address)); break;
        default : throw std::runtime_error("UD_OP_MEM with invalid operand size");
        }
        delete address;
        return loaded.copy();
    }
    else if (    (operand.type == UD_OP_CONST)
              || (operand.type == UD_OP_JIMM)
              || (operand.type == UD_OP_IMM))
        return operand_lval(operand.size, operand).copy();

    throw std::runtime_error("invalid operand type ");
}


void QuesoX86 :: operandSet (unsigned int place, Operand * value) {
    struct ud_operand operand = ud_obj.operand[place];

    if (operand.type == UD_OP_REG) {
        switch (operand.base) {
        case UD_R_AH :
        case UD_R_BH :
        case UD_R_CH :
        case UD_R_DH :
            throw std::runtime_error("setting ah/bh/cd/dh unsupported");
            return;
        default :
            break;
        }
        Variable fullreg = fullReg(operand.base);
        ix86->pdi(new InstructionAssign(&fullreg, value));
        return;
    }
    else if (operand.type == UD_OP_MEM) {
        Operand * address = sib(operand);
        Array memory(8, "memory", 32);
        switch (operand.size) {
        case 8  : ix86->pdi(new InstructionStore(&memory, address, value)); break;
        case 16 : ix86->pdi(new InstructionStoreLE16(&memory, address, value)); break;
        case 32 : ix86->pdi(new InstructionStoreLE32(&memory, address, value)); break;
        default : throw std::runtime_error("operandSet invalid operand size");
        }
        delete address;
    }
}


bool QuesoX86 :: cmovcc (const Operand * condition) {
    Variable * dst = dynamic_cast<Variable *> (operandGet(0));
    Operand * src = operandGet(1);

    ix86->pdi(new InstructionIte(dst, condition, src, dst));

    delete dst;
    delete src;

    return true;
}


bool QuesoX86 :: jcc (const Operand * condition) {
    Variable eip(32, "eip");
    Operand * dst = operandGet(0);

    if (ud_obj.operand[0].type == UD_OP_JIMM) {
        Variable tmp(32, "tmp");

        ix86->pdi(new InstructionSignExtend(&tmp, dst));
        ix86->pdi(new InstructionAdd(&tmp, &eip, &tmp));
        ix86->pdi(new InstructionIte(&eip, condition, &tmp, &eip));
    }
    else {
        ix86->pdi(new InstructionIte(&eip, condition, dst, &eip));
    }

    delete dst;

    return true;
}

    
bool QuesoX86 :: add () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);
    Variable tmp = Variable(lhs->g_bits(), "tmp");
    Constant zero = Constant(lhs->g_bits(), 0);
    Variable OF = Variable(1, "OF");
    Variable SF = Variable(1, "SF");
    Variable CF = Variable(1, "CF");
    Variable ZF = Variable(1, "ZF");

    ix86->pdi(new InstructionAdd(&tmp, lhs, rhs));
    ix86->pdi(new InstructionCmpLtu(&CF, &tmp, lhs));
    ix86->pdi(new InstructionCmpEq(&ZF, &tmp, &zero));
    ix86->pdi(new InstructionCmpLts(&SF, &tmp, &zero));

    Variable SFxorOF = Variable(1, "SFxorOF");
    ix86->pdi(new InstructionCmpLts(&SFxorOF, lhs, rhs));
    ix86->pdi(new InstructionXor(&OF, &SFxorOF, &SF));

    operandSet(0, &tmp);

    delete lhs;
    delete rhs;

    return true;
}


    
bool QuesoX86 :: And () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);
    Variable tmp = Variable(lhs->g_bits(), "tmp");

    Constant zero1 = Constant(1, 0);
    Constant zeroBits = Constant(lhs->g_bits(), 0);
    Variable OF = Variable(1, "OF");
    Variable SF = Variable(1, "SF");
    Variable CF = Variable(1, "CF");
    Variable ZF = Variable(1, "ZF");

    // 8-bit immediates are always sign-extended
    if ((ud_obj.operand[1].type == UD_OP_IMM) && (rhs->g_bits() == 8)) {
        Operand * rhs_old = rhs;
        rhs = new Variable(lhs->g_bits(), "tmpRhs");
        ix86->pdi(new InstructionSignExtend((Variable *) rhs, rhs_old));
        delete rhs_old;
    }

    ix86->pdi(new InstructionAnd(&tmp, lhs, rhs));

    ix86->pdi(new InstructionAssign(OF, zero1));
    ix86->pdi(new InstructionAssign(CF, zero1));
    ix86->pdi(new InstructionCmpEq(ZF, tmp, zeroBits));
    ix86->pdi(new InstructionCmpLts(SF, tmp, zeroBits));

    operandSet(0, &tmp);

    delete lhs;
    delete rhs;

    return true;
}


bool QuesoX86 :: call () {
    Variable eip(32, "eip");
    Variable esp(32, "esp");
    Constant four(32, 4);
    Array    memory(8, "memory", 32);

    // push ret addr
    ix86->pdi(new InstructionSub(&esp, &esp, &four));
    ix86->pdi(new InstructionStoreLE32(&memory, &esp, &eip));

    Operand * rhs = operandGet(0);

    if (ud_obj.operand[0].type == UD_OP_JIMM) {
        Variable rhs_sext(32, "rhs_sext");
        ix86->pdi(new InstructionSignExtend(&rhs_sext, rhs));
        ix86->pdi(new InstructionAdd(&eip, &eip, &rhs_sext));
    }
    else
        ix86->pdi(new InstructionAdd(&eip, &eip, rhs));

    delete rhs;

    return true;
}


bool QuesoX86 :: cmova () {
    Variable ZF(1, "ZF");
    Variable notZF(1, "notZF");
    Variable CF(1, "CF");
    Variable notCF(1, "notCF");
    Variable notCFandnotZF(1, "notCFandnotZF");
    Constant one(1, 1);

    ix86->pdi(new InstructionXor(notZF, ZF, one));
    ix86->pdi(new InstructionXor(notCF, CF, one));
    ix86->pdi(new InstructionAnd(notCFandnotZF, notZF, notCF));

    return cmovcc(notCFandnotZF);
}


bool QuesoX86 :: cmovb () {
    return cmovcc(Variable(1, "CF"));
}


bool QuesoX86 :: cmovbe () {
    Variable ZF(1, "ZF");
    Variable CF(1, "CF");
    Variable CForZF(1, "CForZF");

    ix86->pdi(new InstructionOr(CForZF, CF, ZF));

    return cmovcc(CForZF);
}


bool QuesoX86 :: cmovnz () {
    Variable ZF(1, "ZF");
    Variable notZF(1, "notZF");
    Constant one(1, 1);

    ix86->pdi(new InstructionXor(notZF, ZF, one));

    return cmovcc(notZF);
}


bool QuesoX86 :: cmovs () {
    return cmovcc(Variable(1, "SF"));
}


bool QuesoX86 :: cmovz () {
    return cmovcc(Variable(1, "ZF"));
}


bool QuesoX86 :: cmp () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);

    Variable CF(1, "CF");
    Variable ZF(1, "ZF");
    Variable SF(1, "SF");
    Variable OF(1, "OF");
    Variable SFxorOF(1, "SFxorOF");
    Variable tmp(lhs->g_bits(), "tmp");
    Constant zero(lhs->g_bits(), 0);

    Variable sext(lhs->g_bits(), "sext");
    ix86->pdi(new InstructionSignExtend(&sext, rhs));

    ix86->pdi(new InstructionCmpLtu(&CF,          lhs, &sext));
    ix86->pdi(new InstructionCmpLts(&SFxorOF,     lhs, &sext));
    ix86->pdi(new InstructionCmpEq (&ZF,          lhs, &sext));
    ix86->pdi(new InstructionSub   (&tmp,         lhs, &sext));
    ix86->pdi(new InstructionCmpLts(&SF,          &tmp, &zero));
    ix86->pdi(new InstructionXor   (&OF,          &SFxorOF, &SF));

    delete lhs;
    delete rhs;

    return true;
}


bool QuesoX86 :: cwde () {
    Variable ax = getRegister(UD_R_AX);
    Variable eax = getRegister(UD_R_EAX);

    ix86->pdi(new InstructionSignExtend(eax, ax));

    return true;
}


bool QuesoX86 :: dec () {
    Operand * lhs = operandGet(0);

    Variable tmp(lhs->g_bits(), "tmp");
    Constant one(lhs->g_bits(), 1);

    Variable ZF(1, "ZF");
    Variable SF(1, "SF");
    Variable OF(1, "OF");
    Variable SFxorOF(1, "SFxorOF");
    Constant zero(lhs->g_bits(), 0);

    ix86->pdi(new InstructionSub(&tmp, lhs, &one));

    ix86->pdi(new InstructionCmpLts(&SF, &tmp, &zero));
    ix86->pdi(new InstructionCmpEq(&ZF, &tmp, &zero));
    ix86->pdi(new InstructionCmpLts(&SFxorOF, &tmp, lhs));
    ix86->pdi(new InstructionXor(&OF, &SFxorOF, &SF));

    operandSet(0, &tmp);

    delete lhs;

    return true;
}


bool QuesoX86 :: inc () {
    Operand * lhs = operandGet(0);

    Variable tmp(lhs->g_bits(), "tmp");
    Constant one(lhs->g_bits(), 1);

    Variable ZF(1, "ZF");
    Variable SF(1, "SF");
    Variable OF(1, "OF");
    Variable SFxorOF(1, "SFxorOF");
    Constant zero(lhs->g_bits(), 0);

    ix86->pdi(new InstructionAdd(&tmp, lhs, &one));

    ix86->pdi(new InstructionCmpLts(&SF, &tmp, &zero));
    ix86->pdi(new InstructionCmpEq(&ZF, &tmp, &zero));
    ix86->pdi(new InstructionCmpLts(&SFxorOF, &tmp, lhs));
    ix86->pdi(new InstructionXor(&OF, &SFxorOF, &SF));

    operandSet(0, &tmp);

    delete lhs;

    return true;
}


bool QuesoX86 :: ja () {
    Variable CF(1, "CF");
    Variable ZF(1, "ZF");
    Variable CForZF(1, "CForZF");
    Variable notCForZF(1, "notCForZF");
    Constant one(1, 1);

    ix86->pdi(new InstructionOr(&CForZF, &CF, &ZF));
    ix86->pdi(new InstructionXor(&notCForZF, &CForZF, &one));

    return jcc(notCForZF);
}


bool QuesoX86 :: jae () {
    Variable CF(1, "CF");
    Variable notCF(1, "notCF");
    Constant one(1, 1);

    ix86->pdi(new InstructionXor(&notCF, &CF, &one));

    return jcc(&notCF);
}


bool QuesoX86 :: jb () {
    return jcc(Variable(1, "CF"));
}


bool QuesoX86 :: jbe () {
    Variable CF(1, "CF");
    Variable ZF(1, "ZF");
    Variable CForZF(1, "CForZF");

    ix86->pdi(new InstructionOr(&CForZF, &CF, &ZF));

    return jcc(&CForZF);
}


bool QuesoX86 :: jg () {
    Variable SF(1, "SF");
    Variable OF(1, "OF");
    Variable SFeqOF(1, "SFeqOF");
    Variable ZF(1, "ZF");
    Variable notZF(1, "notZF");
    Variable notZFandSFeqOF(1, "notZFandSFeqOF");
    Constant one(1, 1);

    ix86->pdi(new InstructionCmpEq(&SFeqOF, &SF, &OF));
    ix86->pdi(new InstructionXor(&notZF, &ZF, &one));
    ix86->pdi(new InstructionAnd(&notZFandSFeqOF, &notZF, &SFeqOF));

    return jcc(&notZFandSFeqOF);
}


bool QuesoX86 :: jge () {
    Variable SF(1, "SF");
    Variable OF(1, "OF");
    Variable SFeqOF(1, "SFeqOF");

    ix86->pdi(new InstructionCmpEq(&SFeqOF, &SF, &OF));

    return jcc(&SFeqOF);
}


bool QuesoX86 :: jl () {
    Variable SF(1, "SF");
    Variable OF(1, "OF");
    Variable SFxorOF(1, "SFxorOF");

    ix86->pdi(new InstructionXor(&SFxorOF, &SF, &OF));

    return jcc(&SFxorOF);
}


bool QuesoX86 :: jle () {
    Variable ZF(1, "ZF");
    Variable SF(1, "SF");
    Variable OF(1, "OF");
    Variable ZForSFxorOF(1, "ZForSFxorOF");

    ix86->pdi(new InstructionXor(&ZForSFxorOF, &SF, &OF));
    ix86->pdi(new InstructionOr(&ZForSFxorOF, &ZForSFxorOF, &ZF));

    return jcc(&ZForSFxorOF);
}


bool QuesoX86 :: jmp () {
    return jcc(Constant(1, 1));
}


bool QuesoX86 :: jns () {
    Variable SF(1, "SF");
    Variable notSF(1, "notSF");
    Constant one(1, 1);

    ix86->pdi(new InstructionXor(&notSF, &SF, &one));

    return jcc(&notSF);
}


bool QuesoX86 :: jnz () {
    Variable ZF(1, "ZF");
    Variable notZF(1, "notZF");
    Constant one(1, 1);

    ix86->pdi(new InstructionXor(&notZF, &ZF, &one));

    return jcc(&notZF);
}


bool QuesoX86 :: js () {
    return jcc(Variable(1, "SF"));
}


bool QuesoX86 :: jz () {
    return jcc(Variable(1, "ZF"));
}


bool QuesoX86 :: lea () {
    Operand * src = sib(ud_obj.operand[1]);

    operandSet(0, src);

    delete src;

    return true;
}


bool QuesoX86 :: leave () {
    Variable esp(32, "esp");
    Variable ebp(32, "ebp");
    Constant four(32, 4);
    Array memory(8, "memory", 32);

    ix86->pdi(new InstructionAssign(&esp, &ebp));
    ix86->pdi(new InstructionLoadLE32(&ebp, &memory, &esp));
    ix86->pdi(new InstructionAdd(&esp, &esp, &four));

    return true;
}


bool QuesoX86 :: mov () {
    Operand * src = operandGet(1);

    operandSet(0, src);

    delete src;

    return true;
}


bool QuesoX86 :: movd () {
    return mov();
}


bool QuesoX86 :: movsd () {
    Operand * src = operandGet(1);
    Variable tmp(32, "tmp");

    ix86->pdi(new InstructionAssign(&tmp, src));

    operandSet(0, &tmp);

    delete src;

    return true;
}


bool QuesoX86 :: movzx () {
    Operand * src = operandGet(1);
    operandSet(0, src);
    delete src;

    return true;
}


bool QuesoX86 :: nop () {
    return true;
}


bool QuesoX86 :: Not () {
    Operand * src = operandGet(1);
    Variable tmp(src->g_bits(), "tmp");
    Constant ff(src->g_bits(), -1);

    ix86->pdi(new InstructionXor(&tmp, src, &ff));

    operandSet(0, &tmp);

    delete src;

    return true;
}


bool QuesoX86 :: Or () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);
    Variable tmp(lhs->g_bits(), "tmp");

    ix86->pdi(new InstructionSignExtend(&tmp, rhs));
    ix86->pdi(new InstructionOr(&tmp, lhs, &tmp));

    operandSet(0, &tmp);

    delete lhs;
    delete rhs;

    return true;
}


bool QuesoX86 :: pop () {
    Variable tmp(32, "tmp");
    Variable esp(32, "esp");
    Constant four(32, 4);
    Array memory(8, "memory", 32);

    ix86->pdi(new InstructionLoadLE32(&tmp, &memory, &esp));
    ix86->pdi(new InstructionAdd(&esp, &esp, &four));

    operandSet(0, &tmp);

    return true;
}


bool QuesoX86 :: push () {
    Operand * operand = operandGet(0);

    Variable esp(32, "esp");
    Constant four(32, 4);
    Variable sext(32, "sext");
    Array memory(8, "memory", 32);

    ix86->pdi(new InstructionSignExtend(&sext, operand));
    ix86->pdi(new InstructionSub(&esp, &esp, &four));
    ix86->pdi(new InstructionStoreLE32(&memory, &esp, &sext));

    delete operand;

    return true;
}


bool QuesoX86 :: ret () {
    Variable esp(32, "esp");
    Variable eip(32, "eip");
    Constant four(32, 4);
    Array memory(8, "memory", 32);

    ix86->pdi(new InstructionLoadLE32(&eip, &memory, &esp));
    ix86->pdi(new InstructionAdd(&esp, &esp, &four));

    return true;
}


bool QuesoX86 :: shr () {
    Operand * dst = operandGet(0);
    Operand * bits = operandGet(1);
    Variable tmp(dst->g_bits(), "tmp");

    ix86->pdi(new InstructionShr(&tmp, dst, bits));

    Variable CF(1, "CF");
    Variable bitsMinusOne(dst->g_bits(), "bitsMinusOne");
    Constant one(dst->g_bits(), 1);

    Variable OF(1, "OF");
    

    delete dst;
    delete bits;

    return true;
}


bool QuesoX86 :: sub () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);
    Variable tmp(32, "tmp");

    Variable OFTmp(lhs->g_bits(), "OFTmp");
    Constant OFTmpShr(lhs->g_bits(), lhs->g_bits() - 1);
    Variable OF(1, "OF");
    Variable CF(1, "CF");
    Variable ZF(1, "ZF");
    Variable SF(1, "SF");
    Constant zero(lhs->g_bits(), 0);

    ix86->pdi(new InstructionSub(&tmp, lhs, rhs));

    ix86->pdi(new InstructionXor(&OFTmp, &tmp, lhs));
    ix86->pdi(new InstructionShr(&OF, &OFTmp, &OFTmpShr));
    ix86->pdi(new InstructionCmpLtu(&CF, lhs, &tmp));
    ix86->pdi(new InstructionCmpEq(&ZF, &tmp, &zero));
    ix86->pdi(new InstructionCmpLts(&SF, &tmp, &zero));

    operandSet(0, &tmp);

    delete lhs;
    delete rhs;

    return true;
}


bool QuesoX86 :: test () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);
    Variable tmp(lhs->g_bits(), "tmp");

    Variable OF(1, "OF");
    Variable CF(1, "CF");
    Variable ZF(1, "ZF");
    Variable SF(1, "SF");
    Constant zero1(1, 0);
    Constant zero(lhs->g_bits(), 0);

    ix86->pdi(new InstructionAnd(&tmp, lhs, rhs));
    ix86->pdi(new InstructionCmpEq(&ZF, &tmp, &zero));
    ix86->pdi(new InstructionCmpLts(&SF, &tmp, &zero));
    ix86->pdi(new InstructionAssign(&OF, &zero1));
    ix86->pdi(new InstructionAssign(&SF, &zero1));

    delete lhs;
    delete rhs;

    return 1;
}


bool QuesoX86 :: Xor () {
    Operand * lhs = operandGet(0);
    Operand * rhs = operandGet(1);
    Variable tmp(32, "tmp");

    Variable OF(1, "OF");
    Variable CF(1, "CF");
    Variable SF(1, "SF");
    Variable ZF(1, "ZF");
    Constant zero1(1, 0);
    Constant zero(lhs->g_bits(), 0);

    ix86->pdi(new InstructionXor(&tmp, lhs, rhs));
    ix86->pdi(new InstructionAssign(&OF, &zero));
    ix86->pdi(new InstructionAssign(&CF, &zero));
    ix86->pdi(new InstructionCmpEq(&ZF, &tmp, &zero));
    ix86->pdi(new InstructionCmpLts(&SF, &tmp, &zero));

    operandSet(0, &tmp);

    delete lhs;
    delete rhs;

    return true;
}