"""
Mini Compiler
Effat Habiba
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
import ply.lex as lex
import ply.yacc as yacc
import re

# ============================================================================
# LEXICAL ANALYZER (LEX)
# ============================================================================

class Lexer:
    # Reserved keywords
    reserved = {
        'if': 'IF',
        'else': 'ELSE',
        'while': 'WHILE',
        'for': 'FOR',
        'int': 'INT',
        'float': 'FLOAT',
        'return': 'RETURN',
        'print': 'PRINT',
    }

    # Token list
    tokens = [
        'ID', 'NUMBER', 'FLOAT_NUM',
        'PLUS', 'MINUS', 'TIMES', 'DIVIDE', 'MODULO',
        'ASSIGN', 'EQ', 'NE', 'LT', 'LE', 'GT', 'GE',
        'LPAREN', 'RPAREN', 'LBRACE', 'RBRACE',
        'SEMICOLON', 'COMMA',
    ] + list(reserved.values())

    # Token rules
    t_PLUS = r'\+'
    t_MINUS = r'-'
    t_TIMES = r'\*'
    t_MODULO = r'%'
    t_ASSIGN = r'='
    t_EQ = r'=='
    t_NE = r'!='
    t_LT = r'<'
    t_LE = r'<='
    t_GT = r'>'
    t_GE = r'>='
    t_LPAREN = r'\('
    t_RPAREN = r'\)'
    t_LBRACE = r'\{'
    t_RBRACE = r'\}'
    t_SEMICOLON = r';'
    t_COMMA = r','

    # Ignored characters (spaces and tabs)
    t_ignore = ' \t'

    # Comments - Must be defined before DIVIDE token
    def t_COMMENT_MULTI(self, t):
        r'/\*(.|\n)*?\*/'
        t.lexer.lineno += t.value.count('\n')
        pass  # No return value. Token discarded

    def t_COMMENT_SINGLE(self, t):
        r'//.*'
        pass  # No return value. Token discarded

    # DIVIDE token - Must come after comment rules
    def t_DIVIDE(self, t):
        r'/'
        return t

    def t_FLOAT_NUM(self, t):
        r'\d+\.\d+'
        t.value = float(t.value)
        return t

    def t_NUMBER(self, t):
        r'\d+'
        t.value = int(t.value)
        return t

    def t_ID(self, t):
        r'[a-zA-Z_][a-zA-Z_0-9]*'
        t.type = self.reserved.get(t.value, 'ID')
        return t

    def t_newline(self, t):
        r'\n+'
        t.lexer.lineno += len(t.value)

    def t_error(self, t):
        self.errors.append(f"Illegal character '{t.value[0]}' at line {t.lineno}")
        t.lexer.skip(1)

    def __init__(self):
        self.lexer = None
        self.tokens_list = []
        self.errors = []

    def build(self):
        self.lexer = lex.lex(module=self)

    def tokenize(self, data):
        self.tokens_list = []
        self.errors = []
        self.lexer.input(data)
        
        while True:
            tok = self.lexer.token()
            if not tok:
                break
            self.tokens_list.append({
                'type': tok.type,
                'value': tok.value,
                'line': tok.lineno,
                'position': tok.lexpos
            })
        
        return self.tokens_list, self.errors


# ============================================================================
# SYMBOL TABLE
# ============================================================================

class SymbolTable:
    def __init__(self):
        self.symbols = {}
        self.scope_stack = ['global']
        self.scope_counter = 0
        
    def enter_scope(self, scope_type='block'):
        """Enter a new scope (e.g., if, while, for, block)"""
        self.scope_counter += 1
        scope_name = f"{scope_type}_{self.scope_counter}"
        self.scope_stack.append(scope_name)
        return scope_name
    
    def exit_scope(self):
        """Exit the current scope"""
        if len(self.scope_stack) > 1:
            self.scope_stack.pop()
    
    def get_current_scope(self):
        """Get the current scope name"""
        return self.scope_stack[-1]
        
    def insert(self, name, symbol_type, value=None, scope=None):
        """Insert a symbol into the current scope"""
        if scope is None:
            scope = self.scope_stack[-1]
        
        key = f"{scope}:{name}"
        
        # Check if variable already exists in current scope
        if key in self.symbols:
            return False  # Already declared in this scope
        
        self.symbols[key] = {
            'name': name,
            'type': symbol_type,
            'value': value,
            'scope': scope
        }
        return True
    
    def lookup(self, name):
        """Look up a symbol starting from the current scope and moving up"""
        for scope in reversed(self.scope_stack):
            key = f"{scope}:{name}"
            if key in self.symbols:
                return self.symbols[key]
        return None
    
    def lookup_current_scope(self, name):
        """Look up a symbol only in the current scope"""
        scope = self.scope_stack[-1]
        key = f"{scope}:{name}"
        return self.symbols.get(key, None)
    
    def get_all(self):
        """Get all symbols"""
        return list(self.symbols.values())


# ============================================================================
# PARSER AND SEMANTIC ANALYZER
# ============================================================================

class Parser:
    tokens = Lexer.tokens
    
    def __init__(self):
        self.symbol_table = SymbolTable()
        self.intermediate_code = []
        self.temp_count = 0
        self.label_count = 0
        self.errors = []
        self.parse_tree = []
        
    def new_temp(self):
        self.temp_count += 1
        return f"t{self.temp_count}"
    
    def new_label(self):
        self.label_count += 1
        return f"L{self.label_count}"
    
    def emit(self, op, arg1=None, arg2=None, result=None):
        code = {'op': op, 'arg1': arg1, 'arg2': arg2, 'result': result}
        self.intermediate_code.append(code)
        return result
    
    # Grammar rules
    def p_program(self, p):
        '''program : statement_list'''
        p[0] = ('program', p[1])
        self.parse_tree.append(p[0])
    
    def p_statement_list(self, p):
        '''statement_list : statement_list statement
                         | statement'''
        if len(p) == 3:
            p[0] = p[1] + [p[2]]
        else:
            p[0] = [p[1]]
    
    def p_statement(self, p):
        '''statement : declaration
                    | assignment
                    | print_statement
                    | if_statement
                    | while_statement
                    | block'''
        p[0] = p[1]
    
    def p_declaration(self, p):
        '''declaration : type ID SEMICOLON
                      | type ID ASSIGN expression SEMICOLON'''
        var_type = p[1]
        var_name = p[2]
        
        # Check if variable already exists in current scope
        if self.symbol_table.lookup_current_scope(var_name):
            self.errors.append(f"Variable '{var_name}' already declared in current scope")
        else:
            current_scope = self.symbol_table.get_current_scope()
            if len(p) == 4:
                self.symbol_table.insert(var_name, var_type)
                p[0] = ('declaration', var_type, var_name, current_scope)
            else:
                value = p[4]
                self.symbol_table.insert(var_name, var_type, value)
                self.emit('=', value, None, var_name)
                p[0] = ('declaration_init', var_type, var_name, value, current_scope)
    
    def p_type(self, p):
        '''type : INT
               | FLOAT'''
        p[0] = p[1]
    
    def p_assignment(self, p):
        '''assignment : ID ASSIGN expression SEMICOLON'''
        var_name = p[1]
        expr = p[3]
        
        # Check if variable is declared in any accessible scope
        if not self.symbol_table.lookup(var_name):
            self.errors.append(f"Variable '{var_name}' not declared")
        
        self.emit('=', expr, None, var_name)
        p[0] = ('assignment', var_name, expr)
    
    def p_print_statement(self, p):
        '''print_statement : PRINT LPAREN expression RPAREN SEMICOLON'''
        self.emit('print', p[3], None, None)
        p[0] = ('print', p[3])
    
    def p_if_statement(self, p):
        '''if_statement : IF LPAREN condition RPAREN block
                       | IF LPAREN condition RPAREN block ELSE block'''
        cond = p[3]
        true_label = self.new_label()
        false_label = self.new_label()
        end_label = self.new_label()
        
        self.emit('if_false', cond, false_label, None)
        self.emit('label', true_label, None, None)
        
        if len(p) == 6:
            self.emit('goto', end_label, None, None)
            self.emit('label', false_label, None, None)
        else:
            self.emit('label', false_label, None, None)
            self.emit('goto', end_label, None, None)
        
        self.emit('label', end_label, None, None)
        p[0] = ('if', cond, p[5])
    
    def p_while_statement(self, p):
        '''while_statement : WHILE LPAREN condition RPAREN block'''
        start_label = self.new_label()
        end_label = self.new_label()
        
        self.emit('label', start_label, None, None)
        cond = p[3]
        self.emit('if_false', cond, end_label, None)
        self.emit('goto', start_label, None, None)
        self.emit('label', end_label, None, None)
        
        p[0] = ('while', cond, p[5])
    
    def p_block(self, p):
        '''block : LBRACE statement_list RBRACE
                | LBRACE RBRACE'''
        # Enter new scope when opening brace
        scope = self.symbol_table.enter_scope('block')
        
        if len(p) == 4:
            p[0] = ('block', p[2], scope)
        else:
            p[0] = ('block', [], scope)
        
        # Exit scope when closing brace
        self.symbol_table.exit_scope()
    
    def p_condition(self, p):
        '''condition : expression relop expression'''
        temp = self.new_temp()
        self.emit(p[2], p[1], p[3], temp)
        p[0] = temp
    
    def p_relop(self, p):
        '''relop : LT
                | LE
                | GT
                | GE
                | EQ
                | NE'''
        p[0] = p[1]
    
    def p_expression_binop(self, p):
        '''expression : expression PLUS term
                     | expression MINUS term'''
        temp = self.new_temp()
        self.emit(p[2], p[1], p[3], temp)
        p[0] = temp
    
    def p_expression_term(self, p):
        '''expression : term'''
        p[0] = p[1]
    
    def p_term_binop(self, p):
        '''term : term TIMES factor
               | term DIVIDE factor
               | term MODULO factor'''
        temp = self.new_temp()
        self.emit(p[2], p[1], p[3], temp)
        p[0] = temp
    
    def p_term_factor(self, p):
        '''term : factor'''
        p[0] = p[1]
    
    def p_factor_number(self, p):
        '''factor : NUMBER
                 | FLOAT_NUM'''
        p[0] = p[1]
    
    def p_factor_id(self, p):
        '''factor : ID'''
        if not self.symbol_table.lookup(p[1]):
            self.errors.append(f"Variable '{p[1]}' not declared")
        p[0] = p[1]
    
    def p_factor_paren(self, p):
        '''factor : LPAREN expression RPAREN'''
        p[0] = p[2]
    
    def p_error(self, p):
        if p:
            self.errors.append(f"Syntax error at '{p.value}' (line {p.lineno})")
        else:
            self.errors.append("Syntax error at EOF")
    
    def build(self):
        self.parser = yacc.yacc(module=self)
    
    def parse(self, data):
        self.intermediate_code = []
        self.temp_count = 0
        self.label_count = 0
        self.errors = []
        self.parse_tree = []
        self.symbol_table = SymbolTable()  # Reset symbol table
        
        result = self.parser.parse(data)
        return result


# ============================================================================
# CODE GENERATOR (Assembly)
# ============================================================================

class CodeGenerator:
    def __init__(self):
        self.assembly_code = []
        self.registers = ['R1', 'R2', 'R3', 'R4']
        self.reg_map = {}
        self.next_reg = 0
        
    def get_register(self, var):
        if var in self.reg_map:
            return self.reg_map[var]
        
        reg = self.registers[self.next_reg % len(self.registers)]
        self.next_reg += 1
        self.reg_map[var] = reg
        return reg
    
    def generate(self, intermediate_code):
        self.assembly_code = []
        self.assembly_code.append("; Assembly Code Generated")
        self.assembly_code.append("section .data")
        self.assembly_code.append("section .text")
        self.assembly_code.append("global _start")
        self.assembly_code.append("_start:")
        
        for instruction in intermediate_code:
            op = instruction['op']
            arg1 = instruction['arg1']
            arg2 = instruction['arg2']
            result = instruction['result']
            
            if op == '=':
                reg_src = self.get_register(arg1) if isinstance(arg1, str) and arg1[0] == 't' else None
                reg_dest = self.get_register(result)
                
                if reg_src:
                    self.assembly_code.append(f"    MOV {reg_dest}, {reg_src}")
                else:
                    self.assembly_code.append(f"    MOV {reg_dest}, {arg1}")
                    
            elif op in ['+', '-', '*', '/', '%']:
                reg1 = self.get_register(arg1) if isinstance(arg1, str) else None
                reg2 = self.get_register(arg2) if isinstance(arg2, str) else None
                reg_result = self.get_register(result)
                
                op_map = {'+': 'ADD', '-': 'SUB', '*': 'MUL', '/': 'DIV', '%': 'MOD'}
                
                if reg1 and reg2:
                    self.assembly_code.append(f"    {op_map[op]} {reg_result}, {reg1}, {reg2}")
                elif reg1:
                    self.assembly_code.append(f"    {op_map[op]} {reg_result}, {reg1}, {arg2}")
                elif reg2:
                    self.assembly_code.append(f"    {op_map[op]} {reg_result}, {arg1}, {reg2}")
                else:
                    self.assembly_code.append(f"    {op_map[op]} {reg_result}, {arg1}, {arg2}")
                    
            elif op in ['<', '<=', '>', '>=', '==', '!=']:
                reg1 = self.get_register(arg1) if isinstance(arg1, str) else None
                reg2 = self.get_register(arg2) if isinstance(arg2, str) else None
                reg_result = self.get_register(result)
                
                val1 = reg1 if reg1 else arg1
                val2 = reg2 if reg2 else arg2
                
                self.assembly_code.append(f"    CMP {val1}, {val2}")
                self.assembly_code.append(f"    SET{op} {reg_result}")
                
            elif op == 'label':
                self.assembly_code.append(f"{arg1}:")
                
            elif op == 'goto':
                self.assembly_code.append(f"    JMP {arg1}")
                
            elif op == 'if_false':
                reg = self.get_register(arg1) if isinstance(arg1, str) else None
                val = reg if reg else arg1
                self.assembly_code.append(f"    CMP {val}, 0")
                self.assembly_code.append(f"    JE {arg2}")
                
            elif op == 'print':
                reg = self.get_register(arg1) if isinstance(arg1, str) else None
                val = reg if reg else arg1
                self.assembly_code.append(f"    PRINT {val}")
        
        self.assembly_code.append("    MOV EAX, 1")
        self.assembly_code.append("    INT 0x80")
        
        return self.assembly_code


# ============================================================================
# MINIMAL GUI APPLICATION
# ============================================================================

class CompilerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Mini Compiler")
        self.root.geometry("1200x700")
        self.root.configure(bg='white')
        
        # Initialize compiler components
        self.lexer = Lexer()
        self.lexer.build()
        self.parser = Parser()
        self.parser.build()
        self.code_generator = CodeGenerator()
        
        self.setup_ui()
        
    def setup_ui(self):
        # Title bar
        title_frame = tk.Frame(self.root, bg='#f5f5f5', height=50)
        title_frame.pack(fill=tk.X, padx=0, pady=0)
        title_frame.pack_propagate(False)
        
        title = tk.Label(title_frame, text="Mini Compiler", 
                        font=('Arial', 16, 'bold'), bg='#f5f5f5', fg='#333')
        title.pack(pady=12)
        
        # Main container
        main_container = tk.Frame(self.root, bg='white')
        main_container.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Input section
        input_frame = tk.Frame(main_container, bg='white')
        input_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        
        input_label = tk.Label(input_frame, text="Source Code", 
                              font=('Arial', 11, 'bold'), bg='white', fg='#333')
        input_label.pack(anchor='w', pady=(0, 5))
        
        self.input_text = scrolledtext.ScrolledText(
            input_frame, 
            font=('Consolas', 10),
            bg='#fafafa',
            fg='#333',
            relief=tk.SOLID,
            borderwidth=1,
            padx=8,
            pady=8
        )
        self.input_text.pack(fill=tk.BOTH, expand=True)
        
        # Comprehensive sample code with all features
        sample_code = """// Single-line comment test
/* Multi-line comment test
   This demonstrates comment handling */

// Global variables
int globalX = 100;
int globalY = 200;

// Arithmetic operations test
int sum = globalX + globalY;
int diff = globalY - globalX;
int product = globalX * 2;
int quotient = globalY / 10;
int remainder = globalY % 3;

print(sum);      // Should print 300
print(diff);     // Should print 100
print(product);  // Should print 200

// Conditional statement with scoped variables
if (globalX < globalY) {
    // Variables inside if block (local scope)
    int localA = 50;
    int localB = 75;
    int localSum = localA + localB;
    print(localSum);  // Should print 125
}

/* Test else block with different scope */
if (globalX > 500) {
    int temp = 1;
} else {
    // This is a separate scope
    int temp = 2;  // Different from temp in if block
    int result = temp * 10;
    print(result);  // Should print 20
}

// While loop with scoped counter
int outerCounter = 0;
while (outerCounter < 3) {
    // Loop body creates new scope
    int loopVar = outerCounter * 10;
    print(loopVar);
    outerCounter = outerCounter + 1;
}

// Nested blocks to test scope depth
{
    int level1 = 10;
    {
        int level2 = 20;
        int combined = level1 + level2;  // Can access level1
        print(combined);  // Should print 30
    }
    // level2 is not accessible here
}

// Float operations
float pi = 3.14;
float radius = 5.0;
float area = pi * radius;
print(area);

// Complex expression
int a = 10;
int b = 5;
int c = 3;
int result = a + b * c - a / b;  // Tests operator precedence
print(result);  // Should print 23 (10 + 15 - 2)

// Relational operators test
if (a == 10) {
    print(1);
}

if (b != 10) {
    print(2);
}

if (a >= b) {
    print(3);
}

if (b <= a) {
    print(4);
}

// Final message
int done = 1;
print(done);
"""
        self.input_text.insert('1.0', sample_code)
        
        # Button section
        button_frame = tk.Frame(main_container, bg='white')
        button_frame.pack(fill=tk.X, pady=10)
        
        compile_btn = tk.Button(
            button_frame, 
            text="Compile", 
            command=self.compile_code,
            font=('Arial', 10),
            bg='#007bff',
            fg='white',
            relief=tk.FLAT,
            padx=30,
            pady=8,
            cursor='hand2'
        )
        compile_btn.pack(side=tk.LEFT, padx=(0, 10))
        
        clear_btn = tk.Button(
            button_frame, 
            text="Clear", 
            command=self.clear_all,
            font=('Arial', 10),
            bg='#6c757d',
            fg='white',
            relief=tk.FLAT,
            padx=30,
            pady=8,
            cursor='hand2'
        )
        clear_btn.pack(side=tk.LEFT)
        
        # Output section with tabs
        output_frame = tk.Frame(main_container, bg='white')
        output_frame.pack(fill=tk.BOTH, expand=True)
        
        output_label = tk.Label(output_frame, text="Output", 
                               font=('Arial', 11, 'bold'), bg='white', fg='#333')
        output_label.pack(anchor='w', pady=(0, 5))
        
        # Create notebook for tabs
        style = ttk.Style()
        style.theme_use('default')
        style.configure('TNotebook', background='white', borderwidth=0)
        style.configure('TNotebook.Tab', padding=[12, 8], font=('Arial', 9))
        
        self.notebook = ttk.Notebook(output_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)
        
        # Create tabs
        self.create_output_tab("Tokens", "tokens_text")
        self.create_output_tab("Symbol Table", "symbol_text")
        self.create_output_tab("Intermediate Code", "intermediate_text")
        self.create_output_tab("Assembly", "assembly_text")
        self.create_output_tab("Errors", "errors_text")
        
    def create_output_tab(self, title, attr_name):
        frame = tk.Frame(self.notebook, bg='white')
        self.notebook.add(frame, text=title)
        
        text_widget = scrolledtext.ScrolledText(
            frame,
            font=('Consolas', 9),
            bg='#fafafa',
            fg='#333',
            relief=tk.SOLID,
            borderwidth=1,
            padx=8,
            pady=8
        )
        text_widget.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        setattr(self, attr_name, text_widget)
        
    def compile_code(self):
        source_code = self.input_text.get('1.0', tk.END)
        
        # Clear previous outputs
        for attr in ['tokens_text', 'symbol_text', 'intermediate_text', 
                     'assembly_text', 'errors_text']:
            getattr(self, attr).delete('1.0', tk.END)
        
        # Lexical Analysis
        tokens, lex_errors = self.lexer.tokenize(source_code)
        
        token_output = "Token Type       Value           Line\n"
        token_output += "-" * 45 + "\n"
        for token in tokens:
            token_output += f"{token['type']:<16} {str(token['value']):<15} {token['line']}\n"
        
        self.tokens_text.insert('1.0', token_output)
        
        # Syntax and Semantic Analysis
        self.parser.parse(source_code)
        
        # Symbol Table
        symbol_output = "Name             Type       Scope\n"
        symbol_output += "-" * 45 + "\n"
        for symbol in self.parser.symbol_table.get_all():
            symbol_output += f"{symbol['name']:<16} {symbol['type']:<10} {symbol['scope']}\n"
        
        self.symbol_text.insert('1.0', symbol_output)
        
        # Intermediate Code
        ic_output = ""
        for i, inst in enumerate(self.parser.intermediate_code, 1):
            op = inst['op']
            arg1 = inst['arg1']
            arg2 = inst['arg2']
            result = inst['result']
            
            if op == '=':
                ic_output += f"{i}. {result} = {arg1}\n"
            elif op in ['+', '-', '*', '/', '%']:
                ic_output += f"{i}. {result} = {arg1} {op} {arg2}\n"
            elif op == 'label':
                ic_output += f"{i}. {arg1}:\n"
            elif op == 'goto':
                ic_output += f"{i}. goto {arg1}\n"
            elif op == 'if_false':
                ic_output += f"{i}. if_false {arg1} goto {arg2}\n"
            elif op == 'print':
                ic_output += f"{i}. print {arg1}\n"
            else:
                ic_output += f"{i}. {result} = {arg1} {op} {arg2}\n"
        
        self.intermediate_text.insert('1.0', ic_output)
        
        # Assembly Code
        assembly = self.code_generator.generate(self.parser.intermediate_code)
        assembly_output = "\n".join(assembly)
        self.assembly_text.insert('1.0', assembly_output)
        
        # Errors
        all_errors = lex_errors + self.parser.errors
        if all_errors:
            errors_output = ""
            for i, error in enumerate(all_errors, 1):
                errors_output += f"{i}. {error}\n"
            self.errors_text.insert('1.0', errors_output)
        else:
            self.errors_text.insert('1.0', "✓ No errors found. Compilation successful!")
        
    def clear_all(self):
        self.input_text.delete('1.0', tk.END)
        for attr in ['tokens_text', 'symbol_text', 'intermediate_text', 
                     'assembly_text', 'errors_text']:
            getattr(self, attr).delete('1.0', tk.END)


# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    root = tk.Tk()
    app = CompilerGUI(root)
    root.mainloop()
