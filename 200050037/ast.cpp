#include "ast.hh"
#include <cstdarg>
//////////////////////////////

// statement_astnode::statement_astnode()
// {
// }
/////////////////////////////
int addl = 0;
int val1;
string regs[6] = {"eax","edx","ebx","ecx","edi","esi"};
int cfr =1;
int pf;
int lnum = 2;
int flnum;
int aval=0;
int aioffset;
int aivalue;
int marrsize;
int marrayref = 0;
int la = 0;
int pcpf = 0;
int ai = 0;
int fcao = 0;
int dl = 0;
int aao = 0;
int m2aro = 0;
int m2 = 0;


empty_astnode::empty_astnode() : statement_astnode()
{
	astnode_type = EmptyNode;
}

void empty_astnode::print(int ntabs)
{
	cout << "\"empty\"" << endl;
}

void empty_astnode::gencode(int a)
{
	cout << "";
}

//////////////////////////

seq_astnode::seq_astnode() : statement_astnode()
{

	astnode_type = SeqNode;
}

void seq_astnode::pushback(statement_astnode *child)
{
	children_nodes.push_back(child);
}

void seq_astnode::print(int ntabs)
{
	printblanks(ntabs);
	printAst("", "l", "seq", &children_nodes);
}

void seq_astnode::gencode(int a)
{
	cout << "" ;
	if (a==5 || a==6) {aval = a; flnum = lnum;}
	if (a == 6) { aval = 6; cfr = 2;}
	gencodeAst("", "l", "seq", &children_nodes);
	if (a==5 || a==6) {cout << ".L" << flnum << ":"<< endl;}
}

///////////////////////////////////

assignS_astnode::assignS_astnode(exp_astnode *l, exp_astnode *r, string tc) : statement_astnode()
{
	typecast = tc;
	left = l;
	right = r;
	id = "Ass";
	astnode_type = AssNode;
}

void assignS_astnode::print(int ntabs)
{
	cout << " in assignS_print \n";
	printAst("assignS", "aa", "left", left, "right", right);
}

void assignS_astnode::gencode(int a)
{
	cout << "";
	//gencodeAst("assignS", "a", "left", left, "right", right);
	if (((left -> astnode_type == IdentifierNode && !(left -> is_array)) || left -> astnode_type == MemberNode) && right -> astnode_type != IntConstNode && right -> astnode_type != IdentifierNode) {
		left -> gencode(0);
		right -> gencode(0);
		if (right -> astnode_type == ArrayRefNode && aval == 6) {cout << "\tmovl\t"; dl = 1; right -> gencode(6); cout << ",\t%eax\n";}
		if (marrayref == 1) {
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			cfr = cfr+1;
			left -> gencode(2);
			cfr = cfr -1;
			marrayref = 0;
			cout << "\tmovl\t%" << regs[cfr] << ",\t(%eax)\n";
		}
		if (marrayref != 1) {cout << "\tmovl\t%eax,\t" << left -> offset << "(%ebp)" << endl;}
		m2aro = 0; marrayref = 0;
	}
	if (((left -> astnode_type == IdentifierNode && !(left -> is_array)) || left -> astnode_type == MemberNode) && (right -> astnode_type == IdentifierNode || right -> astnode_type == MemberNode)) {
		left -> gencode(0);
		m2aro = 0;
		if (marrayref == 1) {
			left -> gencode(2);
			cout << "\tmovl\t" << right -> offset << "(%ebp),\t%" << regs[cfr] << endl;
			cout << "\tmovl\t%" << regs[cfr] << ",\t(%eax)\n";
		}
		if (marrayref != 1) {
			cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tmovl\t%eax,\t" << left -> offset << "(%ebp)" << endl;
		}
		m2aro = 0; marrayref = 0;
	}
	else if (((left -> astnode_type == IdentifierNode && !(left -> is_array)) || left -> astnode_type == MemberNode) && right -> astnode_type == IntConstNode) {
		left -> gencode(0);
		if (marrayref == 1) {left -> gencode(2); cout << "\tmovl\t$"; right -> gencode(0); cout << ",\t(%eax)\n";}
		if (marrayref != 1) {
			cout << "\tmovl\t$"; right -> gencode(0);
			cout << ",\t" <<left -> offset << "(%ebp)" << endl;
		}
		m2aro = 0; marrayref = 0;
	}
	if (left -> astnode_type == OpUnaryNode && right -> astnode_type == OpUnaryNode) {
		right -> gencode(0);
		cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
		left -> gencode(2);
		cout << "\tmovl\t%" << regs[cfr] << ",\t(%eax)" << endl;
	}
	else if (left -> astnode_type == OpUnaryNode && ((right -> astnode_type == IdentifierNode && !(right -> is_array)) || right -> astnode_type == MemberNode)) {
		cout << "\tmovl\t" << right -> offset << "(%ebp),\t%" << regs[cfr] << endl;
		left -> gencode(2);
		cout << "\tmovl\t%" << regs[cfr] << ",\t(%eax)" << endl;
	}
	else if (left -> astnode_type == OpUnaryNode && right -> astnode_type == IntConstNode) {
		left -> gencode(2);
		cout << "\tmovl\t$"; right -> gencode(0); cout << ",\t(%eax)" << endl;
	}
	else if (left -> astnode_type == ArrowNode && (right -> astnode_type == IdentifierNode && !(right -> is_array))) {
		cout << "\tmovl\t" << right -> offset << "(%ebp),\t%" << regs[cfr] << endl;
		left -> gencode(2);
		cout << "\tmovl\t%" << regs[cfr] << ",\t%eax" << endl;
	}
	else if (left -> astnode_type == OpUnaryNode && right -> astnode_type == OpBinaryNode) {
		right -> gencode(0);
		cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
		left -> gencode(2);
		cout << "\tmovl\t%" << regs[cfr] << ",\t(%eax)" << endl;
	}
	else if (left -> astnode_type == ArrowNode && right -> astnode_type == IntConstNode) {
		left -> gencode(2);
		cout << "\tmovl\t$"; right -> gencode(0); cout << ",\t"; left -> gencode(3); cout << "(%eax)\n";
	}
	else if (left -> astnode_type == ArrowNode && right -> astnode_type == OpBinaryNode) {
		right -> gencode(0);
		cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
		left -> gencode(2);
		cout << "\tmovl\t%" << regs[cfr] << ",\t"; left -> gencode(3); cout << "(%eax)\n";
	}
	else if (left -> astnode_type == ArrayRefNode && right -> astnode_type == IntConstNode) {
		left -> gencode(5);
		cout << "\tmovl\t$"; right -> gencode(0); cout << ",\t";  left -> gencode(6);
	}
	else if (left -> astnode_type == ArrayRefNode && (right -> astnode_type == IdentifierNode && !(right -> is_array))) {
		cout << "\tmovl\t" << right -> offset <<"(%ebp),\t%" << regs[cfr] << endl;
		cfr = cfr+1;
		left -> gencode(5);
		cfr = cfr-1;
		cout << "\tmovl\t%" << regs[cfr] <<",\t"; cfr = cfr+1; left -> gencode(6); cfr = cfr-1;
	}
	else if (left -> astnode_type == ArrayRefNode && (right -> astnode_type == OpUnaryNode || right -> astnode_type == OpBinaryNode)) {
		right -> gencode(0);
		cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
		cfr = cfr+1;
		left -> gencode(5);
		cfr = cfr-1;
		cout << "\tmovl\t%" << regs[cfr] << ",\t"; cfr = cfr+1; left -> gencode(6); cfr = cfr-1;
		
	}
	else if (left -> astnode_type == ArrayRefNode && right -> astnode_type == ArrayRefNode) {
		right -> gencode(0);
		cout << "\tmovl\t"; dl = 1; right -> gencode(6); cout << ",\t%eax\n";
		cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
		cfr = cfr+1;
		left -> gencode(0);
		cfr = cfr-1;
		cout << "\tmovl\t%" << regs[cfr] << ",\t"; cfr = cfr +1; left -> gencode(6); cfr = cfr -1;
	}
}
///////////////////////////////////

return_astnode::return_astnode(exp_astnode *c) : statement_astnode()
{
	child = c;
	id = "Return";
	astnode_type = ReturnNode;
}
void return_astnode::print(int ntabs)
{
	printAst("", "a", "return", child);
}

void return_astnode::gencode(int a)
{
	cout << "";
	if (child->astnode_type == IntConstNode) {cout << "\tmovl\t$"; child -> gencode(0); cout << "\t,%eax\n";}
	if (child->astnode_type == IdentifierNode && !(child -> is_array)) {cout << "\tmovl\t" << child -> offset << "(%ebp),\t%eax\n";}
	if (child->astnode_type != IntConstNode && child->astnode_type != IdentifierNode) {child->gencode(0);}
	cout << "\tjmp\t.L" << flnum << endl;
}

////////////////////////////////////

if_astnode::if_astnode(exp_astnode *l, statement_astnode *m, statement_astnode *r) : statement_astnode()
{
	left = l;
	middle = m;
	right = r;
	id = "If";
	astnode_type = IfNode;
}

void if_astnode::print(int ntabs)
{
	printAst("if", "aaa",
			 "cond", left,
			 "then", middle,
			 "else", right);
}

void if_astnode::gencode(int a)
{
	int i;
	left -> gencode(0);
	i = lnum;
	cout << "\tcmpl\t$0,\t%eax\n";
	cout << "\tje\t.L" << lnum << endl;
	lnum = lnum+2;
	middle -> gencode(0);
	cout << "\tjmp\t.L" << i+1 << endl;
	cout << ".L" << i << ":\n";
	right -> gencode(0);
	cout << ".L" << i+1 << ":\n";
}
////////////////////////////////////

while_astnode::while_astnode(exp_astnode *l, statement_astnode *r) : statement_astnode()
{
	left = l;
	right = r;
	id = "While";
	astnode_type = WhileNode;
}

void while_astnode::print(int ntabs)
{
	printAst("while", "aa",
			 "cond", left,
			 "stmt", right);
}

void while_astnode::gencode(int a)
{
	int i;
	i = lnum;
	cout << "\tjmp\t.L" << lnum << endl;
	cout << ".L" << lnum+1 << ":\n";
	lnum = lnum+2;
	right -> gencode(0);
	cout << ".L" << i << ":\n";
	left -> gencode(0);
	cout << "\tcmpl\t$0,\t%eax\n";
	cout << "\tjne\t.L" << i+1 << endl;
}
/////////////////////////////////

for_astnode::for_astnode(exp_astnode *l, exp_astnode *m1, exp_astnode *m2, statement_astnode *r) : statement_astnode()
{
	left = l;
	middle1 = m1;
	middle2 = m2;
	right = r;
	id = "For";
	astnode_type = ForNode;
}

void for_astnode::print(int ntabs)
{
	printAst("for", "aaaa",
			 "init", left,
			 "guard", middle1,
			 "step", middle2,
			 "body", right);
}

void for_astnode::gencode(int a)
{
	cout << "";
	int i;
	left -> gencode(0);
	i = lnum;
	cout << "\tjmp\t.L" << lnum << endl;
	cout << ".L" << lnum+1 << ":\n";
	lnum = lnum+2;
	right ->gencode(0);
	middle2 -> gencode(0);
	cout << ".L" << i << ":\n";
	middle1 -> gencode(0);
	cout << "\tcmpl\t$0,%eax\n";
	cout << "\tjne\t.L" << i+1 << endl;
}

//////////////////////////////////

// exp_astnode::exp_astnode() : abstract_astnode()
// {
// }

//////////////////////////////////
string exp_astnode::idname()
{
	return id;
};
op_binary_astnode::op_binary_astnode(string val, exp_astnode *l, exp_astnode *r) : exp_astnode()
{
	id = val;
	left = l;
	right = r;
	astnode_type = OpBinaryNode;
}

void op_binary_astnode::print(int ntabs)
{
	string str = "\"" + id + "\"";
	char *str1 = const_cast<char *>(str.c_str());
	printAst("op_binary", "saa", "op", str1, "left", left, "right", right);
}

void op_binary_astnode::gencode(int a)
{
	
	
	if (((left -> astnode_type == IdentifierNode && !(left -> is_array)) || left -> astnode_type == MemberNode) && ((right -> astnode_type == IdentifierNode && !(right -> is_array)) || right -> astnode_type == MemberNode)) {
		if (id == "PLUS_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%" << regs[cfr] << endl; 
			cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax" << endl; 
			cout << "\taddl\t%" << regs[cfr] << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MULT_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl; 
			cout << "\timull\t" << right -> offset << "(%ebp),\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MINUS_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl; 
			cout << "\tsubl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "DIV_INT") {
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr] << endl; }
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl; 
			cout << "\tcltd\n\tidivl\t" << right -> offset << "(%ebp)" << endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr] << ",\t%edx\n";}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GT_OP_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tcmpl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			if (a==0) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LT_OP_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tcmpl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			if (a==0) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GE_OP_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tcmpl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			if (a==0) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LE_OP_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tcmpl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			if (a==0) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "NE_OP_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tcmpl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			if (a==0) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "EQ_OP_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tcmpl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			if (a==0) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "OR_OP") {
			cout << "\tcmpl\t$0,\t" << left -> offset << "(%ebp)" << endl;
			cout << "\tjne\t.L" << lnum << endl;
			cout << "\tcmpl\t$0,\t" << right -> offset << "(%ebp)" << endl;
			cout << "\tje\t.L" << lnum+1 << endl;
			cout << ".L" << lnum << ":\n\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+2 << endl;
			cout << ".L" << lnum+1 << ":\n\tmovl\t$0,\t%eax\n";
			cout << ".L" << lnum+2 << ":\n";
			lnum = lnum+3;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "AND_OP") {
			cout << "\tcmpl\t$0,\t" << left -> offset << "(%ebp)" << endl;
			cout << "\tje\t.L" <<lnum << endl;
			cout << "\tcmpl\t$0,\t" << right -> offset << "(%ebp)" << endl;
			cout << "\tje\t.L" << lnum << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+1 << "\n.L" <<lnum << ":\n\tmovl\t$0,\t%eax\n.L" << lnum+1 << ":\n";
			lnum = lnum+2;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (((left -> astnode_type == IdentifierNode && !(left -> is_array)) || left -> astnode_type == MemberNode) && right -> astnode_type == IntConstNode) {
		if (id == "PLUS_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\taddl\t$";
			if (left -> deref == 0 ){right -> gencode(0);}
			if (left -> deref == 1 && !left -> istruct){right -> gencode(14);}
			if (left -> deref == 1 && left -> istruct){val1 = left -> issize; right -> gencode(4); cout << val1;}
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MULT_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\timull\t$";
			if (left -> deref == 0 ){right -> gencode(0);}
			if (left -> deref == 1 && !left -> istruct){right -> gencode(14);}
			if (left -> deref == 1 && left -> istruct){val1 = left -> issize; right -> gencode(4); cout << val1;}
			cout << ",\t%eax,\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "DIV_INT") {
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr] << endl;}
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tcdq" << endl;
			cout << "\tmovl\t$"; right->gencode(0); cout << ",\t%esi" << endl;
			cout << "\tidiv\t%esi"<< endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr] << ",\t%edx\n";}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MINUS_INT") {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tsubl\t$";
			if (left -> deref == 0 ){right -> gencode(0);}
			if (left -> deref == 1 && !left -> istruct){right -> gencode(14);}
			if (left -> deref == 1 && left -> istruct){val1 = left -> issize; right -> gencode(4); cout << val1;}
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GT_OP_INT") {
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LT_OP_INT") {
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "NE_OP_INT") {
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "EQ_OP_INT") {
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GE_OP_INT") {
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LE_OP_INT") {
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "OR_OP") {
			cout << "\tcmpl\t$0,\t" << left -> offset << "(%ebp)" << endl;
			cout << "\tjne\t.L" << lnum << endl;
			cout << "\tcmpl\t$0,\t$"; right -> gencode(0); cout << endl;
			cout << "\tje\t.L" << lnum+1 << endl;
			cout << ".L" << lnum << ":\n\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+2 << endl;
			cout << ".L" << lnum+1 << ":\n\tmovl\t$0,\t%eax\n";
			cout << ".L" << lnum+2 << ":\n";
			lnum = lnum+3;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "AND_OP") {
			cout << "\tcmpl\t$0,\t" << left -> offset << "(%ebp)" << endl;
			cout << "\tje\t.L" <<lnum << endl;
			cout << "\tcmpl\t$0,\t$"; right -> gencode(0); cout << endl;
			cout << "\tje\t.L" << lnum << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+1 << "\n.L" <<lnum << ":\n\tmovl\t$0,\t%eax\n.L" << lnum+1 << ":\n";
			lnum = lnum+2;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (((right -> astnode_type == IdentifierNode && !(right -> is_array)) || right -> astnode_type == MemberNode) && left -> astnode_type == IntConstNode) {
		if (id == "PLUS_INT") {
			cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			cout << "\taddl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MULT_INT") {
			cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			cout << "\timull\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MINUS_INT") {
			cout << "\tmovl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			cout << "\tsubl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "DIV_INT") {
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr] << endl;}
			cout << "\tmovl\t$"; left -> gencode(0); cout << ",\t%eax" << endl; 
			cout << "\tcltd\n\tidivl\t" << right -> offset << "(%ebp)" << endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr] << ",\t%edx\n";}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GT_OP_INT") {
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GE_OP_INT") {
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LT_OP_INT") {
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LE_OP_INT") {
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "NE_OP_INT") {
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "EQ_OP_INT") {
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "OR_OP") {
			cout << "\tcmpl\t$0,\t$"; left -> gencode(0); cout << endl;
			cout << "\tjne\t.L" << lnum << endl;
			cout << "\tcmpl\t$0,\t" << right -> offset << "(%ebp)" << endl;
			cout << "\tje\t.L" << lnum+1 << endl;
			cout << ".L" << lnum << ":\n\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+2 << endl;
			cout << ".L" << lnum+1 << ":\n\tmovl\t$0,\t%eax\n";
			cout << ".L" << lnum+2 << ":\n";
			lnum = lnum+3;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "AND_OP") {
			cout << "\tcmpl\t$0,\t$"; left -> gencode(0); cout << endl;
			cout << "\tje\t.L" <<lnum << endl;
			cout << "\tcmpl\t$0,\t" << right -> offset << "(%ebp)" << endl;
			cout << "\tje\t.L" << lnum << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+1 << "\n.L" <<lnum << ":\n\tmovl\t$0,\t%eax\n.L" << lnum+1 << ":\n";
			lnum = lnum+2;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (((left -> astnode_type == IdentifierNode && !(left -> is_array)) || left -> astnode_type == MemberNode) && (right -> astnode_type == OpBinaryNode || right -> astnode_type == OpUnaryNode || right -> astnode_type == FunCallNode || right -> astnode_type == ArrowNode)) {
		if (id == "PLUS_INT") {
			right -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\taddl\t%" << regs[cfr] << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MULT_INT") {
			right -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\timull\t%" << regs[cfr] << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MINUS_INT") {
			right -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tsubl\t%" << regs[cfr] << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "DIV_INT") {
			right -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr+1] << endl;}
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tcltd\n\tidivl\t%" << regs[cfr] << endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr+1] << ",\t%edx" << endl;}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GT_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LT_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GE_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LE_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "NE_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "EQ_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << left -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "OR_OP") {
			cout << "\tcmpl\t$0,\t" << left -> offset << "(%ebp)\n";
			cout << "\tjne\t.L" << lnum+1 << endl;
			right -> gencode(4);
			cout << "\tcmpl\t$0,\t%eax\n\tjne\t.L" << lnum << endl;
			cout << ".L" << lnum << ":\n\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+2 << endl;
			cout << ".L" << lnum+1 << ":\n\tmovl\t$0,\t%eax\n";
			cout << ".L" << lnum+2 << ":\n";
			lnum = lnum+3;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "AND_OP") {
			cout << "\tcmpl\t$0,\t" << left -> offset << "(%ebp)\n";
			cout << "\tje\t.L" << lnum << endl;
			right -> gencode(4);
			cout << "\tcmpl\t$0,\t%eax\n\tjne\t.L" << lnum << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+1 << "\n.L" << lnum << ":\n\tmovl\t$0,\t%eax\n.L" << lnum+1 << ":\n";
			lnum = lnum+2;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (((right -> astnode_type == IdentifierNode && !(right -> is_array)) || right -> astnode_type == MemberNode) && (left -> astnode_type == OpBinaryNode || left -> astnode_type == OpUnaryNode || left -> astnode_type == FunCallNode || left -> astnode_type == ArrowNode)) {
		if (id == "PLUS_INT") {
			left -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr]  << endl;
			cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			cout << "\taddl\t%" << regs[cfr] << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MULT_INT") {
			left -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax" << endl;
			cout << "\timull\t%" << regs[cfr] << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MINUS_INT") {
			left -> gencode(0);
			cout << "\tmovl\t" << right -> offset << "(%ebp),\t%" << regs[cfr] << endl;
			cout << "\tsubl\t%" << regs[cfr] << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "DIV_INT") {
			left -> gencode(0); 
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr] << endl;}
			cout << "\tcltd\n\tidivl\t" << right -> offset << "(%ebp)" << endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr] << ",\t%edx" << endl;}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GT_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LT_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GE_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LE_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "NE_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "EQ_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t%eax,\t" << right -> offset << "(%ebp)" << endl;
			if (a==0) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "OR_OP") {
			left -> gencode(3);
			cout << "\tcmpl\t$0,\t%eax\n\tjne\t.L" << lnum << endl;
			cout << "\tcmpl\t$0,\t" << right -> offset << "(%ebp)\n";
			cout << "\tje\t.L" << lnum+1 << endl;
			cout << ".L" << lnum << ":\n\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+2 << endl;
			cout << ".L" << lnum+1 << ":\n\tmovl\t$0,\t%eax\n";
			cout << ".L" << lnum+2 << ":\n";
			lnum = lnum+3;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "AND_OP") {
			left -> gencode(4);
			cout << "\tcmpl\t$0,\t%eax\n\tjne\t.L" << lnum << endl;
			cout << "\tcmpl\t$0,\t" << right -> offset << "(%ebp)\n";
			cout << "\tje\t.L" << lnum << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+1 << "\n.L" << lnum << ":\n\tmovl\t$0,\t%eax\n.L" << lnum+1 << ":\n";
			lnum = lnum+2;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if ((right -> astnode_type == OpBinaryNode || right -> astnode_type == OpUnaryNode || right -> astnode_type == FunCallNode || right -> astnode_type == ArrowNode) && (left -> astnode_type == OpBinaryNode || left -> astnode_type == OpUnaryNode || left -> astnode_type == FunCallNode || left -> astnode_type == ArrowNode)) {
		if (id == "PLUS_INT") {
			left -> gencode(0);
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tmovl\t%eax,\t%" << regs[1] << endl;}
			else {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\taddl\t%" << regs[1] << ",\t%eax" << endl;}
			else {cout << "\taddl\t%" << regs[cfr] << ",\t%eax" << endl;}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MULT_INT") {
			left -> gencode(0);
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tmovl\t%eax,\t%" << regs[1] << endl;}
			else {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\taddl\t%" << regs[1] << ",\t%eax" << endl;}
			else {cout << "\timull\t%" << regs[cfr] << ",\t%eax" << endl;}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MINUS_INT") {
			left -> gencode(0);
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tmovl\t%eax,\t%" << regs[1] << endl;}
			else {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tsubl\t%eax,\t%" << regs[1] << endl;
			cout << "\tmovl\t%" << regs[1] <<",\t%eax" << endl;}
			else {cout << "\tsubl\t%eax,\t%" << regs[cfr] << endl;
			cout << "\tmovl\t%" << regs[cfr] <<",\t%eax" << endl;}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "DIV_INT") {
			left -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			cout << "\tmovl\t%eax,\t%" << regs[cfr+1] << endl;
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr+2] << endl;}
			cout << "\tmovl\t%" << regs[cfr] << ",\t%eax" << endl;
			cout << "\tcltd\n\tidivl\t%" << regs[cfr+1] << endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr+2] << ",\t%edx" << endl;}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GT_OP_INT") {
			left -> gencode(0);
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tmovl\t%eax,\t%" << regs[1] << endl;}
			else {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tcmpl\t%eax,\t%" << regs[1] << "\n";}
			else {cout << "\tcmpl\t%eax,\t%" << regs[cfr] << "\n";}
			if (a==0) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LT_OP_INT") {
			left -> gencode(0);
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tmovl\t%eax,\t%" << regs[1] << endl;}
			else {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tcmpl\t%eax,\t%" << regs[1] << "\n";}
			else {cout << "\tcmpl\t%eax,\t%" << regs[cfr] << "\n";}
			if (a==0) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GE_OP_INT") {
			left -> gencode(0);
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tmovl\t%eax,\t%" << regs[1] << endl;}
			else {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
			cfr = cfr-1;
			right -> gencode(0);
			cfr = cfr+1;
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tcmpl\t%eax,\t%" << regs[1] << "\n";}
			else {cout << "\tcmpl\t%eax,\t%" << regs[cfr] << "\n";}
			if (a==0) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LE_OP_INT") {
			left -> gencode(0);
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tmovl\t%eax,\t%" << regs[1] << endl;}
			else {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tcmpl\t%eax,\t%" << regs[1] << "\n";}
			else {cout << "\tcmpl\t%eax,\t%" << regs[cfr] << "\n";}
			if (a==0) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "NE_OP_INT") {
			left -> gencode(0);
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tmovl\t%eax,\t%" << regs[1] << endl;}
			else {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tcmpl\t%eax,\t%" << regs[1] << "\n";}
			else {cout << "\tcmpl\t%eax,\t%" << regs[cfr] << "\n";}
			if (a==0) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "EQ_OP_INT") {
			left -> gencode(0);
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tmovl\t%eax,\t%" << regs[1] << endl;}
			else {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			if (right -> astnode_type == FunCallNode && left -> astnode_type == FunCallNode && aval == 6) {cout << "\tcmpl\t%eax,\t%" << regs[1] << "\n";}
			else {cout << "\tcmpl\t%eax,\t%" << regs[cfr] << "\n";}
			if (a==0) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "OR_OP") {
			int i;
			left -> gencode(3);
			i = lnum;
			cout << "\tcmpl\t$0,\t%eax\n\tjne\t.L" << lnum << endl;
			lnum = lnum+3;
			right -> gencode(4);
			cout << "\tcmpl\t$0,\t%eax\n\tjne\t.L" << i+1 << endl;
			cout << ".L" << i << ":\n\tmovl\t$1,\t%eax\n\tjmp\t.L" << i+2 << endl;
			cout << ".L" << i+1 << ":\n\tmovl\t$0,\t%eax\n";
			cout << ".L" << i+2 << ":\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "AND_OP") {
			int i;
			left -> gencode(4);
			i = lnum;
			cout << "\tcmpl\t$0,\t%eax\n\tjne\t.L" << lnum << endl;
			lnum = lnum+2;
			right -> gencode(4);
			cout << "\tcmpl\t$0,\t%eax\n\tjne\t.L" << i << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << i+1 << "\n.L" << i << ":\n\tmovl\t$0,\t%eax\n.L" << i+1 << ":\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if ((left -> astnode_type == OpBinaryNode|| left -> astnode_type == OpUnaryNode || left -> astnode_type == FunCallNode || left -> astnode_type == ArrowNode) && right -> astnode_type == IntConstNode) {
		if (id == "PLUS_INT") {
			left -> gencode(0);
			cout << "\taddl\t$";
			right -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MULT_INT") {
			left -> gencode(0);
			cout << "\timull\t$";
			right -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MINUS_INT") {
			left -> gencode(0);
			cout << "\tsubl\t$";
			right -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "DIV_INT") {
			left -> gencode(0);
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr] << endl;}
			cout << "\tcdq" << endl;
			cout << "\tmovl\t$"; right->gencode(0); cout << ",\t%esi" << endl;
			cout << "\tidiv\t%esi" << endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr] << ",\t%edx" << endl;}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GT_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LT_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "NE_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "EQ_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GE_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LE_OP_INT") {
			left -> gencode(0);
			cout << "\tcmpl\t$";
			right -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "OR_OP") {
			left -> gencode(3);
			cout << "\tcmpl\t$0,\t%eax" << endl;
			cout << "\tjne\t.L" << lnum << endl;
			cout << "\tcmpl\t$0,\t$"; right -> gencode(0); cout << endl;
			cout << "\tje\t.L" << lnum+1 << endl;
			cout << ".L" << lnum << ":\n\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+2 << endl;
			cout << ".L" << lnum+1 << ":\n\tmovl\t$0,\t%eax\n";
			cout << ".L" << lnum+2 << ":\n";
			lnum = lnum+3;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "AND_OP") {
			left -> gencode(4);
			cout << "\tcmpl\t$0,\t" << left -> offset << "(%ebp)" << endl;
			cout << "\tjne\t.L" <<lnum << endl;
			cout << "\tcmpl\t$0,\t$"; right -> gencode(0); cout << endl;
			cout << "\tje\t.L" << lnum << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+1 << "\n.L" <<lnum << ":\n\tmovl\t$0,\t%eax\n.L" << lnum+1 << ":\n";
			lnum = lnum+2;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if ((right -> astnode_type == OpBinaryNode || right -> astnode_type == OpUnaryNode || right -> astnode_type == FunCallNode || right -> astnode_type == ArrowNode) && left -> astnode_type == IntConstNode) {
		if (id == "PLUS_INT") {
			right -> gencode(0);
			cout << "\taddl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MULT_INT") {
			right -> gencode(0);
			cout << "\timull\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MINUS_INT") {
			right -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			cout << "\tmovl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			cout << "\tsubl\t%" << regs[cfr] << ",\t%eax\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "DIV_INT") {
			right -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr+1] << endl;}
			cout << "\tmovl\t$"; left -> gencode(0); cout << ",\t%eax" << endl; 
			cout << "\tcltd\n\tidivl\t%" << regs[cfr] << endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr+1] << ",\t%edx\n";}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GT_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GE_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LT_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "LE_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "NE_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "EQ_OP_INT") {
			right -> gencode(0);
			cout << "\tcmpl\t$";
			left -> gencode(0);
			cout << ",\t%eax" << endl;
			if (a==0) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==4) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "OR_OP") {
			right -> gencode(4);
			cout << "\tcmpl\t$0,\t$"; left -> gencode(0); cout << endl;
			cout << "\tjne\t.L" << lnum << endl;
			cout << "\tcmpl\t$0,\t%eax" << endl;
			cout << "\tjne\t.L" << lnum+1 << endl;
			cout << ".L" << lnum << ":\n\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+2 << endl;
			cout << ".L" << lnum+1 << ":\n\tmovl\t$0,\t%eax\n";
			cout << ".L" << lnum+2 << ":\n";
			lnum = lnum+3;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "AND_OP") {
			right -> gencode(4);
			cout << "\tcmpl\t$0,\t$"; left -> gencode(0); cout << endl;
			cout << "\tje\t.L" <<lnum << endl;
			cout << "\tcmpl\t$0,\t%eax" << endl;
			cout << "\tjne\t.L" << lnum << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+1 << "\n.L" <<lnum << ":\n\tmovl\t$0,\t%eax\n.L" << lnum+1 << ":\n";
			lnum = lnum+2;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (right -> astnode_type == IntConstNode && left -> astnode_type == IntConstNode) {
		
		if (id == "PLUS_INT") {
			val1 = 0; left -> gencode(3); right -> gencode(3);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==1) {cout << "\tpushl\t%eax\n";}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MULT_INT") {
			val1 = 1; left -> gencode(4); right -> gencode(4);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==1) {cout << "\tpushl\t%eax\n";}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "MINUS_INT") {
			val1 = 0; right -> gencode(5); left -> gencode(5);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==1) {cout << "\tpushl\t%eax\n";}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "DIV_INT") {
			val1 = 1; left -> gencode(4); right -> gencode(6);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==1) {cout << "\tpushl\t%eax\n";}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (id == "GT_OP_INT") {
			val1 = 1; left -> gencode(4); right -> gencode(7);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetg\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tjg\t";}
			if (a==4) {cout << "\tjle\t";}
		}
		if (id == "LT_OP_INT") {
			val1 = 1; left -> gencode(4); right -> gencode(8);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetl\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tjl\t";}
			if (a==4) {cout << "\tjge\t";}
		}
		if (id == "GE_OP_INT") {
			val1 = 1; left -> gencode(4); right -> gencode(9);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetge\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tjge\t";}
			if (a==4) {cout << "\tjl\t";}
		}
		if (id == "LE_OP_INT") {
			val1 = 1; left -> gencode(4); right -> gencode(10);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetle\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tjgle\t";}
			if (a==4) {cout << "\tjg\t";}
		}
		if (id == "NE_OP_INT") {
			val1 = 1; left -> gencode(4); right -> gencode(11);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==0) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsetne\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tjgne\t";}
			if (a==4) {cout << "\tje\t";}
		}
		if (id == "EQ_OP_INT") {
			val1 = 1; left -> gencode(4); right -> gencode(12);
			cout << "\tmovl\t$" << val1 << ",\t%eax" << endl;
			if (a==0) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			if (a==1) {cout << "\tsete\t%al\n\tmovzbl\t%al,\t%eax\n\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==3) {cout << "\tje\t";}
			if (a==4) {cout << "\tjne\t";}
		}
		if (id == "OR_OP") {
			cout << "\tcmpl\t$0,\t$"; left -> gencode(0); cout << endl;
			cout << "\tjne\t.L" << lnum;
			cout << "\tcmpl\t$0,\t$"; right -> gencode(0); cout << endl;
			cout << "\tje\t.L" << lnum+1;
			cout << ".L" << lnum << ":\n\tmovl\t$1,\t%eax\n\tjmp\t";
			cout << ".L" << lnum+2 << endl ;
			cout << ".L" << lnum+1 << ":\n\tmovl\t$0,\t%eax" << endl;
			cout << ".L" << lnum+2 << ":\n";
			lnum = lnum+3;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}	
		}
		if (id == "AND_OP") {
			cout << "\tcmpl\t$0,\t$"; left -> gencode(0); cout << endl;
			cout << "\tje\t.L" <<lnum << endl;
			cout << "\tcmpl\t$0,\t$"; right -> gencode(0); cout << endl;
			cout << "\tje\t.L" << lnum << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+1 << "\n.L" <<lnum << ":\n\tmovl\t$0,\t%eax\n.L" << lnum+1 << ":\n";
			lnum = lnum+2;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (((left -> astnode_type == IdentifierNode && (left -> is_array)) || left -> astnode_type == MemberNode) && right -> astnode_type == IntConstNode) {
		if (id == "PLUS_INT") {
			cout << "\tleal\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\taddl\t$";
			right -> gencode(14);
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
			la = 1;
		}
		
		if (id == "MINUS_INT") {
			cout << "\tleal\t" << left -> offset << "(%ebp),\t%eax" << endl;
			cout << "\tsubl\t$";
			right -> gencode(14);
			cout << ",\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if ((left -> astnode_type == OpUnaryNode || left -> astnode_type == OpBinaryNode) && right -> astnode_type == ArrayRefNode) {
		if (id == "MULT_INT") {
			left -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl; cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			cout << "\timull\t%" << regs[cfr] << ",\t%eax\n";
		}
	}
	
	/*else if (right -> astnode_type == IdentifierNode && left -> astnode_type == OpUnaryNode) {
		left -> gencode(0);
		if (id == "MINUS_INT") {
			cout << "\tsubl\t" << right -> offset << "(%ebp),\t%eax\n";
		}
		if (id == "PLUS_INT") {
			cout << "\taddl\t" << right -> offset << "(%ebp),\t%eax\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
		}
	}
	
	else if (left -> astnode_type == IdentifierNode && right -> astnode_type == OpUnaryNode) {
		if (id == "MINUS_INT") {
			right -> gencode(0);
			cout << "\tsubl\t%eax,\t" << left -> offset << "(%ebp)\n";
		}
		if (id == "PLUS_INT") {
			right -> gencode(0);
			cout << "\taddl\t" << left -> offset << "(%ebp),\t%eax\n";
		}
		if (id == "MULT_INT") {
			right -> gencode(0);
			cout << "\timull\t" << left -> offset << "(%ebp),\t%eax\n";
		}
		if (id == "AND_OP") {
			cout << "\tcmpl\t$0,\t" << left -> offset << "(%ebp)\n\tje\t.L" << lnum << endl;
			cout << "\tcmpl\t$0,\t";right -> gencode(2) ; cout << "(%ebp)\n\tjne\t.L" << lnum << endl;
			cout << "\tmovl\t$1,\t%eax\n\tjmp\t.L" << lnum+1 << endl;
			cout << ".L" << lnum << ":\n\tmovl\t$0,\t%eax\n.L" << lnum+1 << ":\n";
			lnum = lnum+2;	
		}
	}
	
	else if (left -> astnode_type == OpUnaryNode && right -> astnode_type == OpBinaryNode) {
		if (id == "DIV_INT") {
			right -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr+1] << endl;}
			cfr = cfr+2;
			left -> gencode(0);
			cfr = cfr-2;
			cout << "\tcltd\n\tidivl\t%" << regs[cfr] << endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr+1] << ",\t%edx" << endl;}
		}
	}
	
	else if (right -> astnode_type == OpUnaryNode && left -> astnode_type == OpBinaryNode) {
		if (id == "DIV_INT") {
			right -> gencode(0);
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			if (cfr>1) {cout << "\tmovl\t%edx,\t%" << regs[cfr+1] << endl;}
			cfr = cfr+2;
			left -> gencode(0);
			cfr = cfr-2;
			cout << "\tcltd\n\tidivl\t%" << regs[cfr] << endl;
			if (cfr>1) {cout << "\tmovl\t%" << regs[cfr+1] << ",\t%edx" << endl;}
		}
	}
	
	else if (left -> astnode_type == OpUnaryNode && right -> astnode_type == IntConstNode) {
		if (id == "PLUS_INT") {
			left -> gencode(0);
			cout << "\taddl\t$"; right -> gencode(0); cout << ",\t%eax\n";
		}
	}
	
	else if (right -> astnode_type == OpUnaryNode && left -> astnode_type == IntConstNode) {
		if (id == "PLUS_INT") {
			left -> gencode(0);
			cout << "\taddl\t$"; right -> gencode(0); cout << ",\t%eax\n";
		}
	}
	
	else if (left -> astnode_type == OpUnaryNode && right -> astnode_type == opUnaryNode) {
		if (id == "PLUS_INT") {
			left -> gencode(0);
			cout << "\taddl\t$"; right -> gencode(0); cout << ",\t%eax\n";
		}
	}*/
}

///////////////////////////////////

op_unary_astnode::op_unary_astnode(string val) : exp_astnode()
{
	id = val;
	astnode_type = OpUnaryNode;
}

void op_unary_astnode::print(int ntabs)
{
	string str = "\"" + id + "\"";
	char *str1 = const_cast<char *>(str.c_str());
	printAst("op_unary", "sa", "op", str1, "child", child);
}

void op_unary_astnode::gencode(int a)
{
	cout << "";
	if (id == "UMINUS") {
		if ((child->astnode_type == IdentifierNode && !(child -> is_array))|| child -> astnode_type == MemberNode){
			cout << "\tmovl\t"<< child->offset << "(%ebp),\t%eax\n\tnegl\t%eax\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (child->astnode_type == OpBinaryNode) {
			child -> gencode(0);
			cout << "\tnegl\t%eax\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (child->astnode_type == IntConstNode) {
			cout << "\tmovl\t$"; child->gencode(0); cout << ",\t%eax\n";
			cout << "\tnegl\t%eax\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (id == "NOT") {
		if ((child->astnode_type == IdentifierNode && !(child -> is_array)) || child -> astnode_type == MemberNode){
			cout << "\tcmpl\t$0,\t"<< child->offset << "(%ebp)\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			//if (a==2) {cout << child->offset;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (child->astnode_type == OpBinaryNode) {
			child -> gencode(0);
			cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (child->astnode_type == IntConstNode) {
			cout << "\tmovl\t$"; child->gencode(0); cout << ",\t%eax\n";
			cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (id == "PP") {
		if ((child->astnode_type == IdentifierNode && !(child -> is_array)) || child -> astnode_type == MemberNode){
			cout << "\tmovl\t" << child ->offset << "(%ebp),\t%eax\n\taddl\t$1,\t" << child -> offset << "(%ebp)\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (id == "ADDRESS") {
		if ((child->astnode_type == IdentifierNode && !(child -> is_array)) || child -> astnode_type == MemberNode){
			cout << "\tleal\t" << child ->offset << "(%ebp),\t%eax\n";
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
	
	else if (id == "DEREF") {
		if ((child->astnode_type == IdentifierNode && !(child -> is_array)) || child -> astnode_type == MemberNode){
			cout << "\tmovl\t" << child ->offset << "(%ebp),\t%eax\n";
			if (a!=2) {cout << "\tmovl\t(%eax),\t%eax\n";}
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
		if (child->astnode_type == OpUnaryNode){
			child -> gencode(0);
			cout << "\tmovl\t(%eax),\t%eax" << endl;
			if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
			if (a==4) {cout << "\tcmpl\t$0,\t%eax\n\tsete\t%al\n\tmovzbl\t%al,\t%eax\n";}
		}
	}
}

op_unary_astnode::op_unary_astnode(string val, exp_astnode *l) : exp_astnode()
{
	id = val;
	child = l;
	astnode_type = OpUnaryNode;
}

string op_unary_astnode::getoperator()
{
	return id;
}
///////////////////////////////////

assignE_astnode::assignE_astnode(exp_astnode *l, exp_astnode *r) : exp_astnode()
{
	left = l;
	right = r;
	astnode_type = AssignNode;
}

void assignE_astnode::print(int ntabs)
{
	printAst("assignE", "aa", "left", left, "right", right);
}

void assignE_astnode::gencode(int a)
{
	cout << "";
	if (left -> astnode_type == IdentifierNode && right -> astnode_type != IntConstNode && right -> astnode_type != IdentifierNode) {
		right -> gencode(0);
		cout << "\tmovl\t%eax,\t" << left -> offset << "(%ebp)" << endl;
	}
	if (left -> astnode_type == IdentifierNode && right -> astnode_type == IdentifierNode) {
		cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax" << endl;
		cout << "\tmovl\t%eax,\t" << left -> offset << "(%ebp)" << endl;
	}
	else if (right -> astnode_type == IntConstNode) {cout << "\tmovl\t$"; right -> gencode(0); cout << ",\t" <<left -> offset << "(%ebp)" << endl;}
}

///////////////////////////////////

funcall_astnode::funcall_astnode() : exp_astnode()
{
	astnode_type = FunCallNode;
}

funcall_astnode::funcall_astnode(identifier_astnode *child)
{
	funcname = child;
	astnode_type = FunCallNode;
}

void funcall_astnode::setname(string name)
{
	funcname = new identifier_astnode(name, 0, 0, 0, 0, 0, 0);
}

void funcall_astnode::pushback(exp_astnode *subtree)
{
	children.push_back(subtree);
}

void funcall_astnode::print(int ntabs)
{
	printAst("funcall", "al", "fname", funcname, "params", &children);
}

void funcall_astnode::gencode(int a)
{
	int i = pf;
	int j = addl;
	addl = 0;
	gencodeAst("funcall", "r", "params", &children);
	pf = i;
	cout << "\tcall\t";
	funcname->gencode(2); 
	cout << endl;
	cout << "\taddl\t$" << addl << ",\t%esp" << endl;
	addl = j;
	if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
}

proccall_astnode::proccall_astnode (funcall_astnode *fc)
{
	procname = fc->funcname;
	children = fc->children;
}
void proccall_astnode::print(int ntabs)
{
    printAst("proccall", "al", "fname", procname, "params", &children);
}

void proccall_astnode::gencode(int a)
{
    procname -> gencode(3);
    if (pcpf == 1) {gencodeAst("funcall", "r", "params", &children); pcpf = 0;}
    else {gencodeAst("proccall", "d", "params", &children);}
    cout << "\tcall\t";
    procname->gencode(2); 
    cout << endl;
    cout << "\taddl\t$" << addl << ",\t%esp" << endl;
    addl = 0;
}
/////////////////////////////////////

intconst_astnode::intconst_astnode(int val) : exp_astnode()
{
	value = val;
	astnode_type = IntConstNode;
}

void intconst_astnode::print(int ntabs)
{

	printAst("", "i", "intconst", value);
}

void intconst_astnode::gencode(int a)
{
	if ( a == 0 ){cout << value;}
	if ( a == 1 ){cout << "\tpushl\t$" << value << endl;}
	if ( a == 2 ){cout << value-1;}
	if ( a == 3 ){val1 = val1+value;}
	if ( a == 4 ){val1 = val1*value;}
	if ( a == 5 ){val1 = value-val1;}
	if ( a == 6 ){val1 = val1/value;}
	if ( a == 7 ){val1 = (val1>value);}
	if ( a == 8 ){val1 = (val1<value);}
	if ( a == 9 ){val1 = (val1>=value);}
	if ( a == 10){val1 = (val1<=value);}
	if ( a == 11){val1 = (val1!=value);}
	if ( a == 12){val1 = (val1==value);}
	if ( a == 13){aivalue = value;}
	if ( a == 14){cout << value*4;}
	if ( a == 15){fcao = fcao*4;}
}

/////////////////////////////////////
floatconst_astnode::floatconst_astnode(float val) : exp_astnode()
{
	value = val;
	astnode_type = FloatConstNode;
}

void floatconst_astnode::print(int ntabs)
{
	printAst("", "f", "floatconst", value);
}

void floatconst_astnode::gencode(int a)
{
	cout << "";
}

///////////////////////////////////
stringconst_astnode::stringconst_astnode(string val, int num) : exp_astnode()
{
	value = val;
	numpf = num;
	astnode_type = StringConstNode;
}

void stringconst_astnode::print(int ntabs)
{
	printAst("", "s", "stringconst", stringTocharstar(value));
}

void stringconst_astnode::gencode(int a)
{
	cout << "";
	
	cout << "\tpushl\t$.LC" << numpf << endl;
}

// ref_astnode::ref_astnode() : exp_astnode()
// {
// 	lvalue = true;
// }

/////////////////////////////////

identifier_astnode::identifier_astnode(string val, int off, int isz, bool is_arr, int derf, bool istr, int issz) : ref_astnode()
{
	id = val;
	offset = off;
	isize = isz;
	is_array =is_arr;
	deref = derf;
	istruct = istr;
	issize = issz;
	astnode_type = IdentifierNode;
}

void identifier_astnode::print(int ntabs)
{
	string str = "\"" + id + "\"";
	char *str1 = const_cast<char *>(str.c_str());
	printAst("", "s", "identifier", str1);
}

void identifier_astnode::gencode(int a)
{
	cout << "";
	if (a==1 && isize<=4 && !is_array) {cout << "\tpushl\t" << offset << "(%ebp)" << endl;}
	if (a==1 && isize>4 && !is_array) {
		int nso;
		nso = isize/4;
		for(int i=nso-1; i>=0; i--) {
			cout <<"\tpushl\t" << offset+4*i << "(%ebp)" << endl;
			if (i!=0) {addl = addl+4;}
		}
	}
	if (a==1 && isize>4 && is_array) {
		cout << "\tleal\t" << offset << "(%ebp),\t%eax\n\tpushl\t%eax\n";
	} 
	if (a==2) {cout << id;}
	if (a==3 && id != "printf") {pcpf = 1;}
}

////////////////////////////////

arrayref_astnode::arrayref_astnode(exp_astnode *l, exp_astnode *r, int aoff) : ref_astnode() // again, changed from ref to exp
{
	left = l;
	right = r;
	id = "ArrayRef";
	aoffset = aoff;
	astnode_type = ArrayRefNode;
}

void arrayref_astnode::print(int ntabs)
{
	printAst("arrayref", "aa", "array", left, "index", right);
}

void arrayref_astnode::gencode(int a)
{
	if (left -> astnode_type == IdentifierNode && left -> deref == 0 && aval !=6) {
		if (right -> astnode_type == IntConstNode) {
			if (a==0) {
				right -> gencode(13);
				aioffset = aivalue * aoffset;
				cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax\n";
				cout << "\taddl\t$" << aioffset << ",\t%eax\n";
			}
			if (a==6) {cout << left -> offset << "(%ebp,%eax,4)\n";}
			if (a==1) {cout << "\tpushl\t" << left -> offset << "(%ebp,%eax,4)\n";}
			if (a==8) {
				cout << "\tleal\t" << left -> offset << "(%ebp),%eax\n";
				cout << "\taddl\t$", val1 = aoffset*4; right -> gencode(4);
				fcao = fcao + val1;
				cout << fcao << ",\t%eax\n\tpushl\t%eax\n";
				fcao = 0;
			}
		}
		if (right -> astnode_type == IdentifierNode) {
			if (aval == 5 && a == 0) {
				aioffset = aoffset;
				cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax\n";
				if (marrsize !=0) {cout << "\timull\t$" << marrsize << ",\t%eax\n"; marrsize = 0;} 
				else {cout << "\timull\t$" << aioffset << ",\t%eax\n"; marrsize = 0;}
			}
			else if (a==5) {cout << "\tmovl\t" << right -> offset << "(%ebp),\%eax\n";}
			else if (a==2) {
				if (marrayref == 1) {cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;}
				cout << "\tmovl\t" << right -> offset << "(%ebp),%eax\n";
				cout << "\timull\t$" << left -> issize << ",\t%eax\n";
				if (marrayref == 1) {cout << "\taddl\t%" << regs[cfr] << ",\t%eax\n";}
				if (marrayref != 1) {cout << "\tleal\t" << left -> offset << ",\t%eax\n";}
				m2aro = m2aro + left -> offset;
			}
			else if (a==6) {cout << left -> offset << "(%ebp,%eax,4)\n";}
			else if (a==1) {
				cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax\n";
				cout << "\tpushl\t" << left -> offset << "(%ebp,%eax,4)\n";
			}
			else if (a==7) {cout << "\tpushl\t" << left -> offset << "(%ebp,%eax,4)\n";}
		}
		if (right -> astnode_type == ArrayRefNode) {
			if (a==7) {cout << "\tpushl\t" << left -> offset << "(%ebp,%eax,4)\n";}
			else {
				right -> gencode(0);
				aioffset = aoffset;
				cout << "\timull\t$" << aioffset << ",\t%eax\n";
			}
		}
		if (right -> astnode_type == OpBinaryNode) {
			right -> gencode(0);
			cout << "\tmovl\t" << left -> offset << "(%ebp,%eax,4),\t%eax\n";
		}
	}
	if (left -> astnode_type == ArrayRefNode && aval !=6) {
		if (a!=6 && a!=7 && a!=8) {ai = ai+1; left -> gencode(0);}
		if (right -> astnode_type == IntConstNode) {
			if (a!=8){
				right -> gencode(13);
				aioffset = aivalue * aoffset;
			}
			if (a!=2) {}
			if (a==6) {cout << aioffset << "(%eax)\n";}
			if (a==1) {cout << "\tpushl\t" << aioffset << "(%eax)\n";}
			if (a==8) {val1 = aoffset*4; right -> gencode(4); fcao = fcao + val1; left -> gencode(8);}
		}
		if (right -> astnode_type == IdentifierNode) {
			if (a==6) {left -> gencode(6);}
			else {
				if (a!=7) {
					aioffset = aoffset;
					cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
					cout << "\tmovl\t" << right -> offset <<"(%ebp),\t%eax\n";
					if (ai>1) {cout << "\timull\t$" << aioffset << ",\t%eax\n";}
					cout << "\taddl\t%" << regs[cfr] << ",\t%eax\n";
				}
				if (a==1 || a==7) {left -> gencode(7);}
			}
		}
		if (right -> astnode_type == ArrayRefNode) {
			cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
			cfr = cfr+1;
			right -> gencode(0);
			cfr = cfr-1;
			cout << "\taddl\t%" << regs[cfr] << ",\t%eax\n";
			if (a==1) {left -> gencode(7);}
		}
	}
	if (left -> astnode_type == MemberNode && aval != 6) {
		if (a==6) {left -> gencode(6);}
		else { 
			if (right -> astnode_type == IdentifierNode) {
				if (marrayref == 1) {
					cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax\n";
					m2 = 1;
					left -> gencode(5);
				}
				if (marrayref != 1) {
					left -> gencode(5);
					cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
					cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax\n";
					cout << "\taddl\t%" << regs[cfr] << ",\t%eax\n";
				}
			}
		}
	}
	if (left -> astnode_type == ArrowNode && aval != 6) {
		if (right -> astnode_type == IdentifierNode) {
			if (a!=6) {
				cout << "\tmovl\t" << right -> offset << "(%ebp),\t%" << regs[cfr] << endl;
				left -> gencode(2);
				if (a==1) {cout << "\tpushl\t"; left -> gencode(6);}
			}
			if (a==6) {left -> gencode(6);}
		}
	}
	
	if (left -> astnode_type == IdentifierNode && aval == 6) {
		if (right -> astnode_type == IdentifierNode) {
			if (a!=6) {
				aioffset = aoffset;
				cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax\n";
				cout << "\timull\t$" << aioffset*4 << ",\t%eax\n";
				cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
				cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax\n";
				cout << "\tleal\t(%" << regs[cfr] << ",%eax),\t%eax\n";
			}
			if (a==6) {cout << "(%" << regs[cfr] << ",%eax)"; if (dl !=1) {cout << endl;} dl = 0;}
		}
		
		if (right -> astnode_type == IntConstNode) {
			aioffset = aoffset;
			if (a!=6) {
				cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax\n";
				if (a==7) {
					cout << "\taddl\t$"; val1 = aioffset*4; right -> gencode(4);
					cout << val1 << ",\t%eax\n";
				}
			}
			if (a==6) {val1 = aioffset*4; right -> gencode(4); cout << val1 << "(%eax)\n";}
			if (a==1) {cout << "\tpushl\t"; val1 = aioffset*4; right -> gencode(4); cout << val1 << "(%eax)\n";}
		}	
	}
	
	if (left -> astnode_type == ArrayRefNode && aval == 6) {
		aioffset = aoffset;
		if (right -> astnode_type == IdentifierNode) {
			int ccfr = cfr;
			if (a!=6) {
				left -> gencode(0);
				cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
				cout << "\tmovl\t" << right -> offset << "(%ebp),\t%eax\n";
			}
			if (a==6) {cout << "(%" << regs[ccfr] << ",%eax,4)"; if (dl !=1) {cout << endl;} dl = 0;}
			if (a==1) {cout << "\tpushl\t(%" << regs[ccfr] << ",%eax,4)\n";}
		}
		if (right -> astnode_type == IntConstNode) {
			if (a!=6) {left -> gencode(7);}
			if (a==6) { val1 = aioffset*4; right -> gencode(4); cout << val1 << "(%eax)\n";}
			if (a==1) {cout << "\tpushl\t"; val1 = aioffset*4; right -> gencode(4); cout << val1 << "(%eax)\n";}
		}
		if (right -> astnode_type == OpBinaryNode) {
			int ccfr = cfr;
			if (a!=6) {
				left -> gencode(0);
				cout << "\tmovl\t%eax,\t%" << regs[cfr] << endl;
				cfr = cfr +1;
				right -> gencode(0);
				cfr = cfr-1;
			}
			if (a==6) {cout << "(%" << regs[ccfr] << ",%eax,4)"; if (dl !=1) {cout << endl;} dl = 0;}
			if (a==1) {cout << "\tpushl\t(%" << regs[ccfr] << ",%eax,4)\n";}
		}
	}
	
	if (left -> astnode_type == ArrowNode && aval == 6) {
		if (right -> astnode_type == IntConstNode) {
			val1 = aoffset * 4;
			right -> gencode(4);
			aao = val1;
			if (a!=6) {left -> gencode(2);}
			if (a!=6 && a!=5) {cout << "\tmovl\t"; left -> gencode(7); cout << ",\t%eax\n";}
			if (a==6) {left -> gencode(7); cout << endl;}
		}
	}
}

///////////////////////////////

// pointer_astnode::pointer_astnode(ref_astnode *c) : ref_astnode()
// {
// 	child = c;
// 	id = "Pointer";
// 	astnode_type = PointerNode;
// }

// void pointer_astnode::print(int ntabs)
// {
// 	printAst("", "a", "pointer", child);
// }

////////////////////////////////

deref_astnode::deref_astnode(ref_astnode *c) : ref_astnode()
{
	child = c;
	id = "Deref";
	astnode_type = DerefNode;
}

void deref_astnode::print(int ntabs)
{
	printAst("", "a", "deref", child);
}

void deref_astnode::gencode(int a)
{
	cout << "";
}

/////////////////////////////////

member_astnode::member_astnode(exp_astnode *l, identifier_astnode *r) // change from ref to exp(1st arg)
{
	left = l;
	right = r;
	astnode_type = MemberNode;
	offset = left -> offset + right -> offset;
}

void member_astnode::print(int ntabs)
{

	printAst("member", "aa", "struct", left, "field", right);
}

void member_astnode::gencode(int a)
{
	if (left -> astnode_type == ArrayRefNode) {
		marrayref = 1;
	}
	if (a==1 && marrayref == 0) {cout << "\tpushl\t" << offset << "(%ebp)" << endl;}
	if (a==5 && m2 != 1) {marrsize = right -> isize /4; left -> gencode(0);}
	if (a==5 && m2 == 1) {cout << "\timull\t$" << right -> issize << ",\t%eax\n"; m2aro = m2aro + right -> offset;left -> gencode(2);}
	if (a==6) {left -> gencode(6);}
	if (left -> astnode_type == ArrayRefNode) {
		marrayref = 1;
		if (a == 2 || a == 1) {
			left -> gencode(2);
			m2aro = m2aro + right -> offset;
			//cout << "\tleal\t" << right -> offset << "(%ebp),\t%eax\n";
			cout << "\tleal\t-4(%ebp),\t%" << regs[cfr] << "\n\taddl\t%eax,\t%" << regs[cfr] << endl;
			cout << "\tleal\t" << m2aro << "(%" << regs[cfr] << "),\t%eax\n";
		}
		if (a == 1) {cout << "\tpushl\t(%eax)\n";}
	}
}

/////////////////////////////////

arrow_astnode::arrow_astnode(exp_astnode *l, identifier_astnode *r)
{
	left = l;
	right = r;
	astnode_type = ArrowNode;
}

void arrow_astnode::print(int ntabs)
{

	printAst("arrow", "aa", "pointer", left, "field", right);
}

void arrow_astnode::gencode(int a)
{
	if (left -> astnode_type == IdentifierNode) {
		if (a == 2) {cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax\n";}
		else if (a==3) {cout << right -> offset;}
		else if (a!=6 && a!=7) {
			cout << "\tmovl\t" << left -> offset << "(%ebp),\t%eax\n\tmovl\t" << right ->offset << "(%eax),\t%eax\n";
		}
		if (a==6) {cout << right -> offset << "(%eax,%" << regs[cfr] << ",4)\n";}
		if (a==1) {cout << "\tmovl\t%eax,\t%" << regs[pf] << endl;}
		if (a==7) {aao = aao + right -> offset; cout << aao << "(%eax)";}
	}
}

void printblanks(int blanks)
{
	for (int i = 0; i < blanks; i++)
		cout << " ";
}

/////////////////////////////////

void gencodeAst(const char *astname, const char *fmt...)
{
	typedef vector<abstract_astnode *> *pv;
	va_list args;
	va_start(args, fmt);
	if ((astname != NULL) && (astname[0] != '\0'))
	{
		
	}
	
	while (*fmt != '\0')
	{
		if (*fmt == 'a')
		{
			abstract_astnode *a = va_arg(args, abstract_astnode *);
			a->gencode(0);
		}
		else if (*fmt == 's')
		{
			
		}
		else if (*fmt == 'i')
		{
			
		}
		else if (*fmt == 'f')
		{
			
		}
		else if (*fmt == 'l')
		{
			lnum = lnum+1;
			char *field = va_arg(args, char *);
			pv f = va_arg(args, pv);
			for (int i = 0; i < (int)f->size(); ++i)
			{
				
				(*f)[i]->gencode(0);
				
				if (i < (int)f->size() - 1)
					cout << "";
				else
					cout << "";
			}

		}
		
		else if (*fmt == 'd')
		{
			char *field = va_arg(args, char *);
			pv f = va_arg(args, pv);
			for (int i = (int)f->size()-1; i >=0 ; --i)
			{
				pf = i;
				if ((*f)[i]->astnode_type != IdentifierNode && (*f)[i]->astnode_type != MemberNode && (*f)[i]->astnode_type != StringConstNode && (*f)[i]->astnode_type != IntConstNode && (*f)[i]->astnode_type != ArrayRefNode){(*f)[i]->gencode(1);}
				addl +=4;	
			}
			for (int i = (int)f->size()-1; i >=0 ; --i)
			{
				pf = i; m2aro = 0;
				if ((*f)[i]->astnode_type != IdentifierNode && (*f)[i]->astnode_type != MemberNode && (*f)[i]->astnode_type != StringConstNode && (*f)[i]->astnode_type != IntConstNode && (*f)[i]->astnode_type != ArrayRefNode){cout << "\tpushl\t%" << regs[pf] << endl;}
				else {(*f)[i]->gencode(1);}
			}
			
		}
		
		else if (*fmt == 'r')
		{
			int j = pf;
			int b=0;
			char *field = va_arg(args, char *);
			pv f = va_arg(args, pv);
			for (int i = 0; i < (int)f->size(); ++i)
			{
				
			}
			for (int i = 0; i < (int)f->size() ; ++i)
			{ 
				if ((*f)[i]->astnode_type != IdentifierNode && (*f)[i]->astnode_type != MemberNode && (*f)[i]->astnode_type != StringConstNode && (*f)[i]->astnode_type != IntConstNode && (*f)[i]->astnode_type != ArrayRefNode)	{
					if (pf == 0 && i==0) {pf = (int)f->size()-1;}
					b = pf;
					if (pf == 1) {pf = (int)f->size();}
					(*f)[i]->gencode(1);
					pf = b;
					pf = pf-1;
					if (i < (int)f->size()-1 && (*f)[i+1]->astnode_type != IdentifierNode && (*f)[i+1]->astnode_type != MemberNode && (*f)[i+1]->astnode_type != StringConstNode && (*f)[i+1]->astnode_type != IntConstNode && (*f)[i+1]->astnode_type != ArrayRefNode) {
						cfr = cfr+1;
					}
				}
				addl +=4;	
			}
			pf = j;
			for (int i = 0; i < (int)f->size() ; ++i)
			{
				if ((*f)[i]->astnode_type != IdentifierNode && (*f)[i]->astnode_type != MemberNode && (*f)[i]->astnode_type != StringConstNode && (*f)[i]->astnode_type != IntConstNode && (*f)[i]->astnode_type != ArrayRefNode)	{
					if (pf == 0 && i==0) {pf = (int)f->size()-1;}
					b = pf;
					if (pf == 1) {pf = (int)f->size();}
					cout << "\tpushl\t%" << regs[pf] << endl;
					pf = b;
					pf = pf-1;
					if (i < (int)f->size()-1 && (*f)[i+1]->astnode_type != IdentifierNode && (*f)[i+1]->astnode_type != MemberNode && (*f)[i+1]->astnode_type != StringConstNode && (*f)[i+1]->astnode_type != IntConstNode && (*f)[i+1]->astnode_type != ArrayRefNode) {
						cfr = cfr-1;
					}
				}
				else {
					if ((*f)[i]->astnode_type != ArrayRefNode){(*f)[i]->gencode(1);}
					else {(*f)[i]->gencode(8);}
				}
			}
			
		}
		
		++fmt;
		if (*fmt != '\0') {}
			
	}
	
	if ((astname != NULL) && (astname[0] != '\0'))
		
	va_end(args);
}

void printAst(const char *astname, const char *fmt...) // fmt is a format string that tells about the type of the arguments.
{
	typedef vector<abstract_astnode *> *pv;
	va_list args;
	va_start(args, fmt);
	if ((astname != NULL) && (astname[0] != '\0'))
	{
		cout << "{ ";
		cout << "\"" << astname << "\""
			 << ": ";
	}
	cout << "{" << endl;
	while (*fmt != '\0')
	{
		if (*fmt == 'a')
		{
			char *field = va_arg(args, char *);
			abstract_astnode *a = va_arg(args, abstract_astnode *);
			
			cout << "\"" << field << "\": " << endl;

			a->print(0);
		}
		else if (*fmt == 's')
		{
			char *field = va_arg(args, char *);
			char *str = va_arg(args, char *);
			
			cout << "\"" << field << "\": ";

			cout << str << endl;
		}
		else if (*fmt == 'i')
		{
			char *field = va_arg(args, char *);
			int i = va_arg(args, int);
			
			cout << "\"" << field << "\": ";

			cout << i;
		}
		else if (*fmt == 'f')
		{
			char *field = va_arg(args, char *);
			double f = va_arg(args, double);
			cout << "\"" << field << "\": ";
			cout << f;
		}
		else if (*fmt == 'l')
		{
			char *field = va_arg(args, char *);
			pv f = va_arg(args, pv);
			
			cout << "\"" << field << "\": ";
			cout << "[" << endl;
			for (int i = 0; i < (int)f->size(); ++i)
			{
				
				(*f)[i]->print(0);
				
				if (i < (int)f->size() - 1)
					cout << endl;
				else
					cout << endl;
			}
			cout << endl;
			cout << "]" << endl;
		}
		++fmt;
		if (*fmt != '\0')
			cout << "" << endl;
	}
	cout << "}" << endl;
	if ((astname != NULL) && (astname[0] != '\0'))
		cout << "}" << endl;
	va_end(args);
}

char *stringTocharstar(string str)
{
	char *charstar = const_cast<char *>(str.c_str());
	return charstar;
}
