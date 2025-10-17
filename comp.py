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

