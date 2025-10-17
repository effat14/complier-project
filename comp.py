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
    t_DIVIDE = r'/'
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
        
    def insert(self, name, symbol_type, value=None, scope=None):
        if scope is None:
            scope = self.scope_stack[-1]
        
        key = f"{scope}:{name}"
        self.symbols[key] = {
            'name': name,
            'type': symbol_type,
            'value': value,
            'scope': scope
        }
    
    def lookup(self, name):
        for scope in reversed(self.scope_stack):
            key = f"{scope}:{name}"
            if key in self.symbols:
                return self.symbols[key]
        return None
    
    def get_all(self):
        return list(self.symbols.values())
        ============================================================================
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
        
        if self.symbol_table.lookup(var_name):
            self.errors.append(f"Variable '{var_name}' already declared")
        else:
            if len(p) == 4:
                self.symbol_table.insert(var_name, var_type)
                p[0] = ('declaration', var_type, var_name)
            else:
                value = p[4]
                self.symbol_table.insert(var_name, var_type, value)
                self.emit('=', value, None, var_name)
                p[0] = ('declaration_init', var_type, var_name, value)
    
    def p_type(self, p):
        '''type : INT
               | FLOAT'''
        p[0] = p[1]
    
    def p_assignment(self, p):
        '''assignment : ID ASSIGN expression SEMICOLON'''
        var_name = p[1]
        expr = p[3]
        
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
        '''block : LBRACE statement_list RBRACE'''
        p[0] = ('block', p[2])
    
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
        
        result = self.parser.parse(data)
        return result

