# bimaru.py: Template para implementação do projeto de Inteligência Artificial 2022/2023.
# Devem alterar as classes e funções neste ficheiro de acordo com as instruções do enunciado.
# Além das funções e classes já definidas, podem acrescentar outras que considerem pertinentes.

# Grupo 47:
# 103145 Nathaniel Prazeres
# 102890 David Nunes

import sys
from search import (
    Problem,
    Node,
    astar_search,
    breadth_first_tree_search,
    depth_first_tree_search,
    greedy_search
)


TOP = ['T', 't']
BOTTOM = ['B', 'b']
LEFT = ['L', 'l']
RIGHT = ['R', 'r']
MIDDLE = ['M', 'm']
CIRCLE = ['C', 'c']
EMPTY_SPACE = [None, '.', 'W']
EMPTY_ADJACENT = [(x, y) for x in EMPTY_SPACE for y in EMPTY_SPACE]

class BimaruState:
    state_id = 0

    def __init__(self, board):
        self.board = board
        self.id = BimaruState.state_id
        BimaruState.state_id += 1

    def __lt__(self, other):
        return self.id < other.id

    def get_board(self) -> 'Board':
        return self.board

####################################################################################################

class Board:
    """Representação interna de um tabuleiro de Bimaru."""
    impossible = False
    num_battleships = 1
    num_cruisers = 2
    num_destroyers = 3
    num_submarines = 4

    def __init__(self, rows: int, cols: int):
        """Construtor: recebe o número de linhas e colunas do tabuleiro."""
        self.rows = rows
        self.cols = cols
        self.board = [[None for _ in range(cols + 1)] for _ in range(rows + 1)] # +1 para guardar os valores totais da linha e coluna

    def set_value(self, row: int, col: int, value):
        """Altera o valor na respetiva posição do tabuleiro."""
        if self.get_value(row, col) is None or isinstance(value, int) or not self.get_value(row, col).isupper():
            self.board[row][col] = value

    def get_value(self, row: int, col: int) -> str or None:
        """Devolve o valor na respetiva posição do tabuleiro."""
        if row < 0 or row >= self.rows or col < 0 or col >= self.cols:
            return None
        return self.board[row][col]

    def get_row_total(self, row: int) -> int:
        """Devolve o número de peças de barco que faltam colocar na linha."""
        return int(self.board[row][self.cols])
    
    def get_col_total(self, col: int) -> int:
        """Devolve o número de peças de barco que faltam colocar na coluna."""
        return int(self.board[self.rows][col])
    
    def lower_total(self, row: int, col: int):
        """Diminui o número de barcos por colocar na linha e coluna."""
        self.set_value(row, self.cols, self.get_row_total(row) - 1)
        self.set_value(self.rows, col, self.get_col_total(col) - 1)

    def copy(self) -> 'Board':
        """Devolve uma cópia do tabuleiro."""
        new_board = Board(self.rows, self.cols)
        new_board.board = [[self.board[row][col] for col in range(self.cols + 1)] for row in range(self.rows + 1)]
        new_board.num_battleships = self.num_battleships
        new_board.num_cruisers = self.num_cruisers
        new_board.num_destroyers = self.num_destroyers
        new_board.num_submarines = self.num_submarines
        return new_board

    def remove_complete_hints(self, list_hints):
        """Remove à lista de barcos quando há uma hint completa."""
        used_hints = []
        for hint in list_hints:
            row, col, cur = hint
            if (row, col) in used_hints:
                continue
            if cur == 'C':
                self.num_submarines -= 1
                used_hints.append((row, col))
            elif cur == 'T':
                if self.get_value(row + 1, col) == 'B':
                    self.num_destroyers -= 1
                    used_hints.append((row, col))
                elif self.get_value(row + 1, col) == 'M':
                    if self.get_value(row + 2, col) == 'B':
                        self.num_cruisers -= 1
                        used_hints.append((row, col))
                    elif self.get_value(row + 2, col) == 'M':
                        if self.get_value(row + 3, col) == 'B':
                            self.num_battleships -= 1
                            used_hints.append((row, col))
            elif cur == 'L':
                if self.get_value(row, col + 1) == 'R':
                    self.num_destroyers -= 1
                    used_hints.append((row, col))
                elif self.get_value(row, col + 1) == 'M':
                    if self.get_value(row, col + 2) == 'R':
                        self.num_cruisers -= 1
                        used_hints.append((row, col))
                    elif self.get_value(row, col + 2) == 'M':
                        if self.get_value(row, col + 3) == 'R':
                            self.num_battleships -= 1
                            used_hints.append((row, col))

    def fill_pos_water(self, row: int, col: int, value: str) -> bool:
        """Preenche as células que são necessáriamente água à volta de uma peça de barco."""
        made_changes = False
        if not value in EMPTY_SPACE:
            if row > 0:
                if col > 0 and self.board[row-1][col-1] is None:
                    self.board[row-1][col-1] = '.'
                    made_changes = True
                if col < self.cols-1 and self.board[row-1][col+1] is None:
                    self.board[row-1][col+1] = '.'
                    made_changes = True
            if row < self.rows-1:
                if col > 0 and self.board[row+1][col-1] is None:
                    self.board[row+1][col-1] = '.'
                    made_changes = True
                if col < self.cols-1 and self.board[row+1][col+1] is None:
                    self.board[row+1][col+1] = '.'
                    made_changes = True
        if value in TOP:
            if self.board[row+1][col] is None:
                self.board[row+1][col] = 'x'
                self.lower_total(row+1, col)
                made_changes = True
            if row > 0 and self.board[row-1][col] is None:
                self.board[row-1][col] = '.'
                made_changes = True
        elif value in BOTTOM:
            if self.board[row-1][col] is None:
                self.board[row-1][col] = 'x'
                self.lower_total(row-1, col)
                made_changes = True
            if row < self.rows-1 and self.board[row+1][col] is None:
                self.board[row+1][col] = '.'
                made_changes = True
        elif value in LEFT:
            if self.board[row][col+1] is None:
                self.board[row][col+1] = 'x'
                self.lower_total(row, col+1)
                made_changes = True
            if col > 0 and self.board[row][col-1] is None:
                self.board[row][col-1] = '.'
                made_changes = True
        elif value in RIGHT:
            if self.board[row][col-1] is None:
                self.board[row][col-1] = 'x'
                self.lower_total(row, col-1)
                made_changes = True
            if col < self.cols-1 and self.board[row][col+1] is None:
                self.board[row][col+1] = '.'
                made_changes = True
        elif value in MIDDLE:
            # Horizontal
            if row == 0 or row == self.rows-1 or self.board[row-1][col] in ('.', 'W') or self.board[row+1][col] in ('.', 'W'):
                if self.board[row][col-1] is None:
                    self.board[row][col-1] = 'x'
                    self.lower_total(row, col-1)
                    made_changes = True
                if self.board[row][col+1] is None:
                    self.board[row][col+1] = 'x'
                    self.lower_total(row, col+1)
                    made_changes = True
            # Vertical
            elif col == 0 or col == self.cols-1 or self.board[row][col-1] in ('.', 'W') or self.board[row][col+1] in ('.', 'W'):
                if self.board[row-1][col] is None:
                    self.board[row-1][col] = 'x'
                    self.lower_total(row-1, col)
                    made_changes = True
                if self.board[row+1][col] is None:
                    self.board[row+1][col] = 'x'
                    self.lower_total(row+1, col)
                    made_changes = True
        elif value in CIRCLE:
            if row > 0 and self.board[row-1][col] is None:
                self.board[row-1][col] = '.'
                made_changes = True
            if row < self.rows-1 and self.board[row+1][col] is None:
                self.board[row+1][col] = '.'
                made_changes = True
            if col > 0 and self.board[row][col-1] is None:
                self.board[row][col-1] = '.'
                made_changes = True
            if col < self.cols-1 and self.board[row][col+1] is None:
                self.board[row][col+1] = '.'
                made_changes = True
        return made_changes

    def fill_board_water(self):
        """Preenche os espaços vazios que são necessáriamente água até não haver mais mudanças."""
        made_changes = True
        while (made_changes):
            made_changes = False
            for row in range(self.rows):
                for col in range(self.cols):
                    if (self.get_row_total(row) == 0 or self.get_col_total(col) == 0) and self.get_value(row, col) is None:
                        self.set_value(row, col, '.')
                        made_changes = True
                    elif self.get_value(row, col) not in EMPTY_SPACE:
                        made_changes = made_changes or self.fill_pos_water(row, col, self.get_value(row, col))
                    elif self.get_row_total(row) < 0 or self.get_col_total(col) < 0:
                        self.impossible = True
                        return

            for row in range(self.rows):
                empty_cols = 0
                for col in range(self.cols):
                    if self.get_value(row, col) is None:
                        empty_cols += 1
                if empty_cols == self.get_row_total(row):
                    for col in range(self.cols):
                        if self.get_value(row, col) is None:
                            if not self.get_value(row, col+1) in (['x'] + EMPTY_SPACE + MIDDLE + RIGHT) or not self.get_value(row, col-1) in (['x'] + EMPTY_SPACE + MIDDLE + LEFT) \
                            or not self.get_value(row+1, col) in (['x'] + EMPTY_SPACE + MIDDLE + BOTTOM) or not self.get_value(row-1, col) in (['x'] + EMPTY_SPACE + MIDDLE + TOP) \
                            or not self.get_value(row+1, col+1) in EMPTY_SPACE or not self.get_value(row+1, col-1) in EMPTY_SPACE or not self.get_value(row-1, col+1) in EMPTY_SPACE or not self.get_value(row-1, col-1) in EMPTY_SPACE:
                                self.impossible = True
                                return
                            self.set_value(row, col, 'x')
                            self.lower_total(row, col)
                            self.fill_pos_water(row, col, 'x')
                            made_changes = True

            for col in range(self.cols):
                empty_rows = 0
                for row in range(self.rows):
                    if self.get_value(row, col) is None:
                        empty_rows += 1
                if empty_rows == self.get_col_total(col):
                    for row in range(self.rows):
                        if self.get_value(row, col) is None:
                            if not self.get_value(row, col+1) in (['x'] + EMPTY_SPACE + MIDDLE + RIGHT) or not self.get_value(row, col-1) in (['x'] + EMPTY_SPACE + MIDDLE + LEFT) \
                            or not self.get_value(row+1, col) in (['x'] + EMPTY_SPACE + MIDDLE + BOTTOM) or not self.get_value(row-1, col) in (['x'] + EMPTY_SPACE + MIDDLE + TOP) \
                            or not self.get_value(row+1, col+1) in EMPTY_SPACE or not self.get_value(row+1, col-1) in EMPTY_SPACE or not self.get_value(row-1, col+1) in EMPTY_SPACE or not self.get_value(row-1, col-1) in EMPTY_SPACE:
                                self.impossible = True
                                return
                            self.set_value(row, col, 'x')
                            self.lower_total(row, col)
                            self.fill_pos_water(row, col, 'x')
                            made_changes = True
        self.complete_unknown()

    def complete_unknown(self):
        """Tenta descobrir se os placeholders conseguem completar um barco."""
        for row in range(self.rows):
            for col in range(self.cols):
                if self.get_value(row, col) == 'x' and (row == 0 or self.get_value(row-1, col) in ('.', 'W')) \
                and (col == 0 or self.get_value(row, col-1) in ('.', 'W')):
                    # Circle
                    if (row == self.rows-1 or self.get_value(row+1, col) in ('.', 'W')) \
                    and (col == self.cols-1 or self.get_value(row, col+1) in ('.', 'W')):
                        self.set_value(row, col, 'c')
                        self.num_submarines -= 1
                        continue
                    # Horizontal
                    size, is_boat = 1, False
                    for i in range(1, 5):
                        if self.get_value(row, col+i) in (['x'] + RIGHT + MIDDLE):
                            size += 1
                        elif self.get_value(row, col+i) in ['.', 'W']:
                            is_boat = True
                            break
                        else:
                            break
                    if is_boat:
                        if size == 4:
                            self.apply_action((row, col, 'lmmr', 'h'))
                        elif size == 3:
                            self.apply_action((row, col, 'lmr', 'h'))
                        elif size == 2:
                            self.apply_action((row, col, 'lr', 'h'))
                    # Vertical
                    size, is_boat = 1, False
                    for i in range(1, 5):
                        if self.get_value(row+i, col) in (['x'] + BOTTOM + MIDDLE):
                            size += 1
                        elif self.get_value(row+i, col) == '.':
                            is_boat = True
                            break
                        else:
                            break
                    if is_boat:
                        if size == 4:
                            self.apply_action((row, col, 'tmmb', 'v'))
                        elif size == 3:
                            self.apply_action((row, col, 'tmb', 'v'))
                        elif size == 2:
                            self.apply_action((row, col, 'tb', 'v'))
                elif self.get_value(row, col) == 'L':
                    size, is_boat, already_complete = 1, False, True
                    for i in range(1, 5):
                        if self.get_value(row, col+i) in (['x'] + RIGHT + MIDDLE):
                            size += 1
                            if self.get_value(row, col+i) != 'x':
                                already_complete = False
                        elif self.get_value(row, col+i) == '.':
                            is_boat = True
                            break
                        else:
                            break
                    if is_boat and not already_complete:
                        if size == 4:
                            self.apply_action((row, col, 'lmmr', 'h'))
                        elif size == 3:
                            self.apply_action((row, col, 'lmr', 'h'))
                        elif size == 2:
                            self.apply_action((row, col, 'lr', 'h'))
                elif self.get_value(row, col) == 'T':
                    size, is_boat, already_complete = 1, False, True
                    for i in range(1, 5):
                        if self.get_value(row+i, col) in (['x'] + BOTTOM + MIDDLE):
                            size += 1
                            if self.get_value(row+i, col) != 'x':
                                already_complete = False
                        elif self.get_value(row+i, col) == '.':
                            is_boat = True
                            break
                        else:
                            break
                    if is_boat and not already_complete:
                        if size == 4:
                            self.apply_action((row, col, 'tmmb', 'v'))
                        elif size == 3:
                            self.apply_action((row, col, 'tmb', 'v'))
                        elif size == 2:
                            self.apply_action((row, col, 'tb', 'v'))
                    

    def possible_actions(self) -> list:
        """Devolve uma lista de ações possíveis."""
        actions = []
        for row in range(self.rows):
            for col in range(self.cols):
                if self.num_battleships > 0:
                    if row < self.rows-3:
                        can_fit = True
                        n_marked, n_placed = 0, 0
                        if (row == 0 or self.get_value(row-1, col) in EMPTY_SPACE) and self.get_value(row, col) in (['x', None] + TOP) \
                        and self.get_value(row+1, col) in (['x', None] + MIDDLE) and self.get_value(row+2, col) in (['x', None] + MIDDLE) \
                        and self.get_value(row+3, col) in (['x', None] + BOTTOM) and (row == self.rows-4 or self.get_value(row+4, col) in EMPTY_SPACE):
                            for i in range(4):
                                if self.get_value(row+i, col) == 'x':
                                    n_marked += 1
                                elif self.get_value(row+i, col) in (TOP + MIDDLE + BOTTOM):
                                    n_placed += 1
                                elif self.get_row_total(row+i) < 1:
                                    can_fit = False
                                    break
                            if n_placed != 4 and self.get_col_total(col) >= (4 - n_marked - n_placed) and can_fit:
                                actions.append((row, col, 'tmmb', 'v'))
                    if col < self.cols-3:
                        can_fit = True
                        n_marked, n_placed = 0, 0
                        if (col == 0 or self.get_value(row, col-1) in EMPTY_SPACE) and self.get_value(row, col) in (['x', None] + LEFT) \
                        and self.get_value(row, col+1) in (['x', None] + MIDDLE) and self.get_value(row, col+2) in (['x', None] + MIDDLE) \
                        and self.get_value(row, col+3) in (['x', None] + RIGHT) and (col == self.cols-4 or self.get_value(row, col+4) in EMPTY_SPACE):
                            for i in range(4):
                                if self.get_value(row, col+i) == 'x':
                                    n_marked += 1
                                elif self.get_value(row, col+i) in (LEFT + MIDDLE + RIGHT):
                                    n_placed += 1
                                elif self.get_col_total(col+i) < 1:
                                    can_fit = False
                                    break
                            if n_placed != 4 and self.get_row_total(row) >= (4 - n_marked - n_placed) and can_fit:
                                actions.append((row, col, 'lmmr', 'h'))
                elif self.num_cruisers > 0:
                    if row < self.rows-2:
                        can_fit = True
                        n_marked, n_placed = 0, 0
                        if (row == 0 or self.get_value(row-1, col) in EMPTY_SPACE) and self.get_value(row, col) in (['x', None] + TOP) \
                        and self.get_value(row+1, col) in (['x', None] + MIDDLE) and self.get_value(row+2, col) in (['x', None] + BOTTOM) \
                        and (row == self.rows-3 or self.get_value(row+3, col) in EMPTY_SPACE):
                            for i in range(3):
                                if self.get_value(row+i, col) == 'x':
                                    n_marked += 1
                                elif self.get_value(row+i, col) in (TOP + MIDDLE + BOTTOM):
                                    n_placed += 1
                                elif self.get_row_total(row+i) < 1:
                                    can_fit = False
                                    break
                            if n_placed != 3 and self.get_col_total(col) >= (3 - n_marked - n_placed) and can_fit:
                                actions.append((row, col, 'tmb', 'v'))
                    if col < self.cols-2:
                        can_fit = True
                        n_marked, n_placed = 0, 0
                        if (col == 0 or self.get_value(row, col-1) in EMPTY_SPACE) and self.get_value(row, col) in (['x', None] + LEFT) \
                        and self.get_value(row, col+1) in (['x', None] + MIDDLE) and self.get_value(row, col+2) in (['x', None] + RIGHT) \
                        and (col == self.cols-3 or self.get_value(row, col+3) in EMPTY_SPACE):
                            for i in range(3):
                                if self.get_value(row, col+i) == 'x':
                                    n_marked += 1
                                elif self.get_value(row, col+i) in (LEFT + MIDDLE + RIGHT):
                                    n_placed += 1
                                elif self.get_col_total(col+i) < 1:
                                    can_fit = False
                                    break
                            if n_placed != 3 and self.get_row_total(row) >= (3 - n_marked - n_placed) and can_fit:
                                actions.append((row, col, 'lmr', 'h'))
                elif self.num_destroyers > 0:
                    if row < self.rows-1:
                        can_fit = True
                        n_marked, n_placed = 0, 0
                        if (row == 0 or self.get_value(row-1, col) in EMPTY_SPACE) and self.get_value(row, col) in (['x', None] + TOP) \
                        and self.get_value(row+1, col) in (['x', None] + BOTTOM) and (row == self.rows-2 or self.get_value(row+2, col) in EMPTY_SPACE):
                            for i in range(2):
                                if self.get_value(row+i, col) == 'x':
                                    n_marked += 1
                                elif self.get_value(row+i, col) in (TOP + BOTTOM):
                                    n_placed += 1
                                elif self.get_row_total(row+i) < 1:
                                    can_fit = False
                                    break
                            if n_placed != 2 and self.get_col_total(col) >= (2 - n_marked - n_placed) and can_fit:
                                actions.append((row, col, 'tb', 'v'))
                    if col < self.cols-1:
                        can_fit = True
                        n_marked, n_placed = 0, 0
                        if (col == 0 or self.get_value(row, col-1) in EMPTY_SPACE) and self.get_value(row, col) in (['x', None] + LEFT) \
                        and self.get_value(row, col+1) in (['x', None] + RIGHT) and (col == self.cols-2 or self.get_value(row, col+2) in EMPTY_SPACE):
                            for i in range(2):
                                if self.get_value(row, col+i) == 'x':
                                    n_marked += 1
                                elif self.get_value(row, col+i) in (LEFT + RIGHT):
                                    n_placed += 1
                                elif self.get_col_total(col+i) < 1:
                                    can_fit = False
                                    break
                            if n_placed != 2 and self.get_row_total(row) >= (2 - n_marked - n_placed) and can_fit:
                                actions.append((row, col, 'lr', 'h'))
                elif self.num_submarines > 0:
                    if (self.get_value(row, col) == 'x' or (self.get_value(row, col) is None \
                    and self.get_row_total(row) >= 1 and self.get_col_total(col) >= 1)) \
                    and (row == self.rows-1 or self.get_value(row+1, col) in EMPTY_SPACE) \
                    and (col == self.cols-1 or self.get_value(row, col+1) in EMPTY_SPACE) \
                    and (row == 0 or self.get_value(row-1, col) in EMPTY_SPACE) \
                    and (col == 0 or self.get_value(row, col-1) in EMPTY_SPACE):
                        actions.append((row, col, 'c', 'h'))
        return actions

    def apply_action(self, action: tuple):
        """Aplica a ação ao tabuleiro."""
        row, col, move, orientation = action
        changed = False
        for i in move:
            if orientation == 'h':
                old_value = self.get_value(row, col)
                if old_value is None:
                    self.lower_total(row, col)
                self.set_value(row, col, i)
                if old_value != self.get_value(row, col):
                    changed = True
                col += 1
            elif orientation == 'v':
                old_value = self.get_value(row, col)
                if old_value is None:
                    self.lower_total(row, col)
                self.set_value(row, col, i)
                if old_value != self.get_value(row, col):
                    changed = True
                row += 1
        if changed:
            if len(move) == 4:
                self.num_battleships -= 1
            elif len(move) == 3:
                self.num_cruisers -= 1
            elif len(move) == 2:
                self.num_destroyers -= 1
            elif len(move) == 1:
                self.num_submarines -= 1
            self.fill_board_water()

    @staticmethod
    def parse_instance(from_input=sys.stdin) -> 'Board':
        """Lê o test do standard input (stdin) que é passado como argumento
        e retorna uma instância da classe Board.

        Por exemplo:
            $ python3 bimaru.py < input_T01

            > from sys import stdin
            > line = stdin.readline().split()
        """
        rows = from_input.readline().split()[1:]
        cols = from_input.readline().split()[1:]
        n_rows = len(rows)
        n_cols = len(cols)
        board = Board(n_rows, n_cols)

        # Para guardar os valores do número de navios que podem estar na linha e coluna
        for row in range(n_rows):
            board.set_value(row, n_cols, rows[row])
        for col in range(n_cols):
            board.set_value(n_rows, col, cols[col])

        n_hints = eval(from_input.readline())
        hints = []
        for _ in range(n_hints):
            hint = from_input.readline().split()[1:]
            board.set_value(int(hint[0]), int(hint[1]), hint[2])
            if hint[2] != 'W':
                hints.append((int(hint[0]), int(hint[1]), hint[2]))
                board.lower_total(int(hint[0]), int(hint[1]))

        board.remove_complete_hints(hints)
        board.fill_board_water()
        return board

    def print_board(self):
        """Imprime o tabuleiro no standard output (stdout)."""
        for row in range(self.rows):
            for col in range(self.cols):
                print(self.board[row][col], end='')
            print()

####################################################################################################

class Bimaru(Problem):
    def __init__(self, board: Board):
        """O construtor especifica o estado inicial."""  
        super().__init__(BimaruState(board))

    def actions(self, state: BimaruState) -> list:
        """Retorna uma lista de ações que podem ser executadas a
        partir do estado passado como argumento."""
        board: Board = state.get_board()
        if board.impossible:
            return []
        actions = board.possible_actions()
        return actions


    def result(self, state: BimaruState, action) -> BimaruState:
        """Retorna o estado resultante de executar a 'action' sobre
        'state' passado como argumento. A ação a executar deve ser uma
        das presentes na lista obtida pela execução de
        self.actions(state)."""
        new_board: Board = state.get_board().copy()
        new_board.apply_action(action)
        new_board.fill_board_water()
        child_state: BimaruState = BimaruState(new_board)
        return child_state
        

    def goal_test(self, state: BimaruState) -> bool:
        """Retorna True se e só se o estado passado como argumento é
        um estado objetivo. Deve verificar se todas as posições do tabuleiro
        estão preenchidas de acordo com as regras do problema."""
        board: Board = state.get_board()
        if board.impossible or board.num_submarines != 0 or board.num_destroyers != 0 or board.num_cruisers != 0 or board.num_battleships != 0:
            return False
        for row in range(board.rows):
            if board.get_row_total(row) != 0:
                return False
            for col in range(board.cols):
                if board.get_col_total(col) != 0 or board.get_value(row, col) is None:
                    return False
        return True

    def h(self, node: Node):
        """Função heuristica utilizada para a procura A*."""
        # Não é usado
        pass

if __name__ == "__main__":
    board: Board = Board.parse_instance()

    problem: Bimaru = Bimaru(board)

    goal_node: Node = depth_first_tree_search(problem)

    goal_node.state.get_board().print_board()
