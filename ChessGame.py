#Chess Game - Agathiyan Bragadeesh

#https://commons.wikimedia.org/wiki/Category:PNG_chess_pieces/Standard_transparent
#Source of piece skins      

#Import modules
import os
import json
import pygame
from PIL import Image, ImageTk
import math
import tkinter
import time
from datetime import datetime
import random
import numpy

##### BOARD REPRESENTATION #####

###Board Class
class Board:
    def __init__(self,turn):
        #Array of the board and will contain the pieces on it
        self.board = [[None,None,None,None,None,None,None,None],
                      [None,None,None,None,None,None,None,None],
                      [None,None,None,None,None,None,None,None],
                      [None,None,None,None,None,None,None,None],
                      [None,None,None,None,None,None,None,None],
                      [None,None,None,None,None,None,None,None],
                      [None,None,None,None,None,None,None,None],
                      [None,None,None,None,None,None,None,None]]
        self.square_identifiers = [[letter + number for number in ['8','7','6','5','4','3','2','1']] for letter in ['a','b','c','d','e','f','g','h']]
        #Loads the image of the board to be displayed
        self.image = pygame.image.load("Textures/Board.png")
        #List of all the pieces on the board
        
        #Initialising black pieces
        bp0 = Pawn(-1,0,1,0,self)
        bp1 = Pawn(-1,1,1,1,self)
        bp2 = Pawn(-1,2,1,2,self)
        bp3 = Pawn(-1,3,1,3,self)
        bp4 = Pawn(-1,4,1,4,self)
        bp5 = Pawn(-1,5,1,5,self)
        bp6 = Pawn(-1,6,1,6,self)
        bp7 = Pawn(-1,7,1,7,self)
        bq = Queen(-1,3,0,8,self)
        bb1 = Bishop(-1,2,0,9,self)
        bb2 = Bishop(-1,5,0,10,self)
        br1 = Rook(-1,0,0,11,self)
        br2 = Rook(-1,7,0,12,self)
        bn1 = Knight(-1,1,0,13,self)
        bn2 = Knight(-1,6,0,14,self)
        bk = King(-1,4,0,15,self)

        #Initialising white pieces
        wp0 = Pawn(1,0,6,16,self)
        wp1 = Pawn(1,1,6,17,self)
        wp2 = Pawn(1,2,6,18,self)
        wp3 = Pawn(1,3,6,19,self)
        wp4 = Pawn(1,4,6,20,self)
        wp5 = Pawn(1,5,6,21,self)
        wp6 = Pawn(1,6,6,22,self)
        wp7 = Pawn(1,7,6,23,self)
        wq = Queen(1,3,7,24,self)
        wb1 = Bishop(1,2,7,25,self)
        wb2 = Bishop(1,5,7,26,self)
        wr1 = Rook(1,0,7,27,self)
        wr2 = Rook(1,7,7,28,self)
        wn1 = Knight(1,1,7,29,self)
        wn2 = Knight(1,6,7,30,self)
        wk = King(1,4,7,31,self)

        #List of all pieces so they can be updated
        self.pieces = [bp0,bp1,bp2,bp3,bp4,bp5,bp6,bp7,bq,bb1,bb2,br1,br2,bn1,bn2,bk,wp0,wp1,wp2,wp3,wp4,wp5,wp6,wp7,wq,wb1,wb2,wr1,wr2,wn1,wn2,wk]
        self.white_king = wk
        self.black_king = bk
        self.initial_turn = turn #If board is created by black AI, board starts with black turn
        self.turn = turn
        self.checkspaces_white = set()
        self.checkspaces_black = set()
        self.list_of_moves = [] #String list of move in notation
        self.record_of_boards = [] #List of boards (not list of moves as list of boards allows for immediate traversal and reversing moves)
        self.move_buffer = str()
        self.in_check = False
        self.endstate = 0 #0 if still in play, -1 if black wins, 1 if white wins, 2 if stalemate
        self.current_index = 0
        self.record_board(self.current_index)
        
    def increment_turn(self):
        if not self.check_check(): #If in a check position after turn is made, invalid move
            self.current_index += 1
            self.record_board(self.current_index)
            self.turn = self.initial_turn * ((-1)**(self.current_index))
            self.in_check = self.check_check() #If player whose turn it is is in check
            self.endstate = self.check_endstate(self.turn * -1)
            self.list_of_moves = self.list_of_moves[0:self.current_index-1]
            self.list_of_moves.append(self.move_buffer)
            self.move_buffer = str()
            if self.endstate == -1 or self.endstate == 1: #Checkmate
                self.list_of_moves[-1] += '#' #Adds checkmate symbol
            elif self.in_check:
                self.list_of_moves[-1] += '+' #Check symbol
            for piece in self.pieces:
                if piece.colour == self.turn and type(piece) == Pawn:
                    piece.double_move = False
            return True
        else:
            self.move_buffer = str()
            self.revert_board(self.current_index)
            return False
        
    def piece(self,x,y):
        return self.board[x][y]
    
    def square_id(self,x,y):
        return self.square_identifiers[x][y]
    
    def piece_set(self,x,y,piece):
        #Sets a piece on board at a specific position
        self.board[x][y] = piece
        
    def promote(self,piece,promote_id):
        self.pieces[piece.identifier] = None
        #promote_id describes the piece to promote to
        if promote_id == 1:
            new_piece = Queen(piece.colour,piece.posx,piece.posy,piece.identifier,self)
        elif promote_id == 2:
            new_piece = Rook(piece.colour,piece.posx,piece.posy,piece.identifier,self)
        elif promote_id == 3:
            new_piece = Bishop(piece.colour,piece.posx,piece.posy,piece.identifier,self)
        elif promote_id == 4:
            new_piece = Knight(piece.colour,piece.posx,piece.posy,piece.identifier,self)
        #0 is only used when reverting board to demoted state
        elif promote_id == 0:
            new_piece = Pawn(piece.colour,piece.posx,piece.posy,piece.identifier,self)
            new_piece.original_pos = False
        new_piece.promoted = promote_id
        piece_to_delete = self.pieces[new_piece.identifier]
        self.pieces[new_piece.identifier] = new_piece
        del piece_to_delete #Deletes old instance of the piece
        
    def check_checkspaces(self):
        #An array of coordinates on the board which the king cannot occupy as that would result in it being in check.
        #checkspaces_white are the spaces the black king can't move to, and checkspaces_black are the spaces the white king can't move to
        self.checkspaces_white = set()
        self.checkspaces_black = set()
        #Following code groups together all the spaces under attack for each colour
        for piece in self.pieces:
            if piece.alive:
                coords = piece.possible_moves() #moves that can be done, if a move can be done to the square the king is on, it must be a capture (i.e. is in check)
                for coord in coords:
                    if piece.colour == -1:
                        self.checkspaces_white.add((coord[0],coord[1]))
                    elif piece.colour == 1:
                        self.checkspaces_black.add((coord[0],coord[1]))
                    
    def check_check(self):
        #Updates checkspaces lists
        self.check_checkspaces()
        #Depending on whose turn it is, either the white king is looked at or the black king is
        if self.turn == 1:
            return (self.white_king.posx,self.white_king.posy) in self.checkspaces_white
        else:
            return (self.black_king.posx,self.black_king.posy) in self.checkspaces_black
        
    def record_board(self,index):
        Record = {}
        #When recording a board, all boards after the index being saved are removed
        self.record_of_boards = self.record_of_boards[0:index]
        for piece in self.pieces:
            piece_type = type(piece)
            Record[str(piece.identifier)] = {}
            Record[str(piece.identifier)]["posx"] = piece.posx
            Record[str(piece.identifier)]["posy"] = piece.posy
            Record[str(piece.identifier)]["alive"] = piece.alive
            #Conditional statements used to assign values to fields specific to certain classes
            if piece_type == Pawn:
                Record[str(piece.identifier)]["original_pos"] = piece.original_pos
                Record[str(piece.identifier)]["double_move"] = piece.double_move
            else:
                Record[str(piece.identifier)]["double_move"] = None
                if piece_type == Rook or piece_type == King:
                    Record[str(piece.identifier)]["original_pos"] = piece.original_pos
                else:
                    Record[str(piece.identifier)]["original_pos"] = None
            Record[str(piece.identifier)]["promoted"] = piece.promoted
        #Record is added to the index
        self.record_of_boards.append(Record)
        
    def revert_board(self,index):
        self.turn = self.initial_turn * ((-1)**(index)) #Since each increment in index is a change in turn, repeated multiplication of the index will get turn
        self.current_index = index
        #Clears every item on the board, and then reverts the attributes of each piece, and sets the piece back in its old position
        for a in range(0,8):
            for b in range(0,8):
                self.piece_set(a,b,None)
        #Gets record from record_of_boards to get data from
        record = self.record_of_boards[index]
        pieces_buffer = self.pieces
        for piece in pieces_buffer:
            #Updates attribute values of objects
            piece_info = record[str(piece.identifier)]
            piece.posx = piece_info["posx"]
            piece.posy = piece_info["posy"]
            piece.alive = piece_info["alive"]
            #Only sets piece on the board if alive
            if piece.alive:
                self.piece_set(piece.posx,piece.posy,piece)
                if piece.promoted != piece_info["promoted"]:
                    self.promote(piece,piece_info["promoted"])
            if type(piece) == Rook or type(piece) == King:
                piece.original_pos = piece_info["original_pos"]
            elif type(piece) == Pawn:
                piece.double_move = piece_info["double_move"]
                piece.original_pos = piece_info["original_pos"]
        self.in_check = self.check_check() #If player whose turn it is is in check
                
    def check_endstate(self,potential_winner): #0 for none, 1 is white wins, -1 if black wins, 2 if stalematem 3 if insufficient material
        game_state = self.check_checkmate(potential_winner)
        if game_state == 0:
            if self.check_insufficient_material():
                return 3
            else:
                return 0
        else:
            return game_state
    
    def check_insufficient_material(self):
        bishop_insufficient = {(Pawn,-1):0,(Knight,-1):0,(Bishop,-1):1,(Rook,-1):0,(Queen,-1):0,(King,-1):1,(Pawn,1):0,(Knight,1):0,(Bishop,1):1,(Rook,1):0,(Queen,1):0,(King,1):1}
        #Tuples represent piece and colour of peice
        material = {(Pawn,-1):0,(Knight,-1):0,(Bishop,-1):0,(Rook,-1):0,(Queen,-1):0,(King,-1):0,(Pawn,1):0,(Knight,1):0,(Bishop,1):0,(Rook,1):0,(Queen,1):0,(King,1):0}
        for piece in self.pieces:
            if piece.alive:
                material[(type(piece),piece.colour)] += 1
        if material == bishop_insufficient:
            #We now know there are only two bishops of opposite colours on the board (and two kings), we can use a logical xor on both their square_colour_black attribute to return if insufficient
            insufficient = True
            #Variable needs to be declared before loop, True is used as (False XOR A) = NOT A
            for piece in self.pieces:
                if piece.alive:
                    if type(piece) == Bishop:
                        insufficient ^= piece.square_colour_black
            #True if insufficient material
            return insufficient
        else:
            #Checks if all of the following pieces have no instances on the board (if the total sum of counts is 0, each individual count is 0)
            total = 0
            for piece_tuple in [(Pawn,-1),(Rook,-1),(Queen,-1),(Pawn,1),(Rook,1),(Queen,1)]:
                total += material[piece_tuple]
            if total == 0:
                #If at least one of following: (Knight,-1) (Bishop,-1) (Knight,1) (Bishop,1), else insufficient
                total = 0
                for piece_tuple in [(Knight,-1),(Bishop,-1),(Knight,1),(Bishop,1)]:
                    total += material[piece_tuple]
                #Returns whether or not there is a total of less than one of listed pieces
                return total <= 1
            else:
                return False
    
    def check_checkmate(self,potential_winner):
        #GameWin is 0 when the game is in play, and the condition of the while loop that keeps the game playing. GameWin will change to either -1 or 1 on checkmate, indicating which colour has won (black or white respectively)
        endstate = potential_winner
        #Goes through every move for each piece
        move_list = [] 
        for piece in self.pieces:
            if piece.colour == potential_winner * -1 and piece.alive:
                for move in piece.possible_moves():
                    move_list.append(MoveObject(piece.identifier,piece.posx,piece.posy,move))
        #Checks every move for every piece (important note, if GameWin remains not equal to 0, this means there are no legal moves, but it doesn't necessarily mean there is currently a check, i.e. a stalemate. This is checked after the loop is broken
        for move in move_list:
            move_success = move.execute(self,True)
            self.check_checkspaces()
            #Checks if after the move, the king is still in check. If not, GameWin is changed back to 0 as there is a valid move remaining.
            if endstate == -1:
                if (not ((self.white_king.posx,self.white_king.posy) in self.checkspaces_white)) and move_success:
                    self.revert_board(self.current_index)
                    return 0
            elif endstate == 1:
                if (not ((self.black_king.posx,self.black_king.posy) in self.checkspaces_black)) and move_success:
                    self.revert_board(self.current_index)
                    return 0
            #If the move was successful, the board is reverted so the next move can be checked
            if move_success:
                self.revert_board(self.current_index)
        if not((self.black_king.posx,self.black_king.posy) in self.checkspaces_black) and not((self.white_king.posx,self.white_king.posy) in self.checkspaces_white):
            return 2                                                                   
        return endstate

    def save_game(self,game_name): #game_name is the name for the game as chosen by the user
        if not os.path.exists("Games"): #Checks if game folder exists, if not the directory is made
            os.mkdir("Games")
        file_name = game_name
        while os.path.isfile("Games/" + file_name + ".json"): #Checks if game has already been saved with same name, else adds a "-" character at the end until file name doesnt exist
            file_name += "-"
        filepath = "Games/" + file_name + ".json"
        game = {}
        game["game_name"] = game_name
        game["list_of_moves"] = self.list_of_moves
        game["record_of_boards"] = self.record_of_boards
        game["datetimeplayedUNIX"] = str(time.time()) #Used to order display of games by datetime
        game["datetimeplayedstring"] = datetime.now().strftime("%d-%m-%Y %H:%M")
        with open(filepath,"w") as savefile:
            json.dump(game,savefile)

    def load_game_to_board(self,file_name):
        with open("Games/" + file_name,"r") as loadfile:
            game = json.load(loadfile)
        self.list_of_moves = game["list_of_moves"]
        self.record_of_boards = game["record_of_boards"]
    
###Piece Classes

#General class, of which all pieces are subclasses of
class ChessPiece:
    def __init__(self,colour,posx,posy,piece,num,board,notation):
        #The pawn's x and y positions, along with a temporary cache for reversion
        self.posx = posx
        self.posy = posy
        self.identifier = num
        self.alive = True
        #Black is -1, White is 1
        if colour == -1:
            self.image = pygame.image.load("Textures/" + piece + "Black.png")
        elif colour == 1:
            self.image = pygame.image.load("Textures/" + piece + "White.png")
        self.colour = colour
        self.promoted = 0 #0 is not promoted, 1 is to a Queen, 2 is to a Rook, 3 is to a Bishop, 4 is to a Rook
        self.board = board
        self.notation = notation
        #Sets piece on the board
        self.board.piece_set(posx,posy,self)
        
    def take(self):
        #Removes itself from the board and the game
        self.board.piece_set(self.posx,self.posy,None)
        self.alive = False      
    
    def piece_move(self,x,y):
        #In the case there is a piece and it is not of the same colour, the knight takes the piece else if it is an empty space, it'll just move there.
        if self.board.piece(x,y) != None:
            self.board.piece(x,y).take() #move has already been checked, so we can be sure it's valid
        #Removes the piece from original position on the board
        self.board.piece_set(self.posx,self.posy,None)
        #Sets new x and y positional values
        self.posx = x
        self.posy = y
        #Sets piece in new position
        self.board.piece_set(x,y,self)
        return True

    def move(self,x,y,is_player_move = True):
        if (x,y) in self.possible_moves():
            #If the move is being run by the check_checkmate() method, adding notation isn't needed
            if is_player_move:
                #Piece notation varies between capture and no capture
                if self.board.piece(x,y) != None:
                    self.board.move_buffer = self.notation + self.board.square_id(self.posx,self.posy) + 'x' + self.board.square_id(x,y)
                else:
                    self.board.move_buffer = self.notation + self.board.square_id(self.posx,self.posy) + '-' + self.board.square_id(x,y)
            #Moves the piece
            return self.piece_move(x,y)
        return False

class Pawn(ChessPiece):
    def __init__(self,colour,posx,posy,num,board):
        ChessPiece.__init__(self,colour,posx,posy,"Pawn",num,board,'')
        self.original_pos = True
        #The double move variable is used to track if the last move on the baord was a double move by this pawn. Used in the en passant.
        self.double_move = False
        
    def move(self,x,y,is_player_move = True):
        if (x,y) in self.possible_moves():
            if self.posx != x: #A capture (move must be diagonal and capture if in a possible move)
                if is_player_move:
                    self.board.move_buffer = self.board.square_id(self.posx,self.posy) + 'x' + self.board.square_id(x,y)
                if self.board.piece(x,y) == None: #This means a diagonal move, no piece at destination square and a valid move means its an en passant
                    self.board.piece(x,self.posy).take()
                    self.original_pos = False
                    return self.piece_move(x,y)
            else: #Not a capture
                if is_player_move:
                    self.board.move_buffer = self.board.square_id(self.posx,self.posy) + '-' + self.board.square_id(x,y)
                if abs(self.posy-y) == 2: #Double moves and en passants are mutually exclusive, elif can therefore be used
                    self.double_move = True #Updates to allow check for en passant
            self.original_pos = False
            return self.piece_move(x,y)
        return False
        
    def possible_moves(self):
        possible_moves_list = []
        #Single move
        if 0<=self.posy-self.colour and 7>=self.posy-self.colour:
            if self.board.piece(self.posx,self.posy-self.colour) == None:
                possible_moves_list.append((self.posx,self.posy-self.colour))
                #Double move
                if self.original_pos:
                    if 0<=self.posy-(2*self.colour) and 7>=self.posy-(2*self.colour):
                        if self.board.piece(self.posx,self.posy-(2*self.colour)) == None:
                            possible_moves_list.append((self.posx,self.posy-(2*self.colour)))
            #Capture 1
            if self.posx <= 6:
                if self.board.piece(self.posx+1,self.posy-self.colour) != None:
                    if self.board.piece(self.posx+1,self.posy-self.colour).colour != self.colour:
                        possible_moves_list.append((self.posx+1,self.posy-self.colour))
                #En passant 1
                elif self.board.piece(self.posx+1,self.posy) != None and self.board.piece(self.posx+1,self.posy).colour != self.colour and type(self.board.piece(self.posx+1,self.posy)) == Pawn:
                    if self.board.piece(self.posx+1,self.posy).double_move:
                        possible_moves_list.append((self.posx+1,self.posy-self.colour))
            #Capture 2
            if self.posx >= 1:
                if self.board.piece(self.posx-1,self.posy-self.colour) != None:
                    if self.board.piece(self.posx-1,self.posy-self.colour).colour != self.colour:
                        possible_moves_list.append((self.posx-1,self.posy-self.colour))
                #En passant 2
                elif self.board.piece(self.posx-1,self.posy) != None and self.board.piece(self.posx-1,self.posy).colour != self.colour and type(self.board.piece(self.posx-1,self.posy)) == Pawn:
                    if self.board.piece(self.posx-1,self.posy).double_move:
                        possible_moves_list.append((self.posx-1,self.posy-self.colour))
        return possible_moves_list

class Knight(ChessPiece):
    def __init__(self,colour,posx,posy,num,board):
        ChessPiece.__init__(self,colour,posx,posy,"Knight",num,board,'N')
        
    def possible_moves(self):
        possible_moves_list = []
        #All possible unordered pairs of movement in the x and y direction
        for vector in [(1,2),(-1,2),(1,-2),(-1,-2),(2,1),(-2,1),(2,-1),(-2,-1)]:
            #Finds vectors that the knight can move to, first taking the first item as the x change and the second item as the y change of the move, then vice versa
            if 0<=self.posx+vector[0] and 7>=self.posx+vector[0] and 0<=self.posy+vector[1] and 7>=self.posy+vector[1]:
                if self.board.piece(self.posx+vector[0],self.posy+vector[1]) != None:
                    if self.board.piece(self.posx+vector[0],self.posy+vector[1]).colour != self.colour:
                        possible_moves_list.append((self.posx+vector[0],self.posy+vector[1]))
                else:
                    possible_moves_list.append((self.posx+vector[0],self.posy+vector[1]))
        return possible_moves_list
    
class Bishop(ChessPiece):
    def __init__(self,colour,posx,posy,num,board):
        ChessPiece.__init__(self,colour,posx,posy,"Bishop",num,board,'B')
        self.square_colour_black = ((posx - posy) % 2 == 0) #Used for insufficient material check
    
    def possible_moves(self):
        possible_moves_list = []
        for (dx,dy) in [(-1,-1),(1,-1),(-1,1),(1,1)]:
            for multiple in range(1,8): #max multiple is 7 if moving across the whole board
                #If out of range break
                if (self.posx + (multiple*dx))>7 or (self.posx + (multiple*dx))<0 or (self.posy + (multiple*dy))>7 or (self.posy + (multiple*dy))<0:
                    break
                #If there is a piece at space, and if it on the same side or opposite side as itself
                elif (self.board.piece(self.posx + (multiple*dx),self.posy + (multiple*dy)) != None):
                    if self.board.piece(self.posx + (multiple*dx),self.posy + (multiple*dy)).alive:
                        if self.board.piece(self.posx + (multiple*dx),self.posy + (multiple*dy)).colour != self.colour:
                            possible_moves_list.append((self.posx + (multiple*dx),self.posy + (multiple*dy)))
                        break
                possible_moves_list.append((self.posx + (multiple*dx),self.posy + (multiple*dy)))
        return possible_moves_list
        #Similar possible_moves method is used for rook and queen, difference being for loop of (dx,dy) is slightly different

class Rook(ChessPiece):
    def __init__(self,colour,posx,posy,num,board):
        ChessPiece.__init__(self,colour,posx,posy,"Rook",num,board,'R')
        #Initialisation, the original_pos attribute is used for castling; castling will be considered an invalid move is original_pos is False, the King has this attribute as well for the same reason.
        self.original_pos = True
    
    def possible_moves(self):
        possible_moves_list = []
        for (dx,dy) in [(-1,0),(1,0),(0,1),(0,-1)]:
            for multiple in range(1,8):
                if (self.posx + (multiple*dx))>7 or (self.posx + (multiple*dx))<0 or (self.posy + (multiple*dy))>7 or (self.posy + (multiple*dy))<0:
                    break
                if (self.board.piece(self.posx + (multiple*dx),self.posy + (multiple*dy)) != None):
                    if self.board.piece(self.posx + (multiple*dx),self.posy + (multiple*dy)).alive:
                        if self.board.piece(self.posx + (multiple*dx),self.posy + (multiple*dy)).colour != self.colour:
                            possible_moves_list.append((self.posx + (multiple*dx),self.posy + (multiple*dy)))
                        break
                possible_moves_list.append((self.posx + (multiple*dx),self.posy + (multiple*dy)))
        return possible_moves_list

    def move(self,x,y,is_player_move = True):
        if (x,y) in self.possible_moves():
            if is_player_move:
                if self.board.piece(x,y) != None:
                    self.board.move_buffer = self.notation + self.board.square_id(self.posx,self.posy) + 'x' + self.board.square_id(x,y)
                else:
                    self.board.move_buffer = self.notation + self.board.square_id(self.posx,self.posy) + '-' + self.board.square_id(x,y)
            self.original_pos = False
            return self.piece_move(x,y)
        return False
    
class Queen(ChessPiece):
    def __init__(self,colour,posx,posy,num,board):
        ChessPiece.__init__(self,colour,posx,posy,"Queen",num,board,'Q')
        
    def possible_moves(self):
        possible_moves_list = []
        for (dx,dy) in [(-1,0),(1,0),(0,1),(0,-1),(-1,-1),(1,-1),(-1,1),(1,1)]:
            for multiple in range(1,8):
                if (self.posx + (multiple*dx))>7 or (self.posx + (multiple*dx))<0 or (self.posy + (multiple*dy))>7 or (self.posy + (multiple*dy))<0:
                    break
                if (self.board.piece(self.posx + (multiple*dx),self.posy + (multiple*dy)) != None):
                    if self.board.piece(self.posx + (multiple*dx),self.posy + (multiple*dy)).alive:
                        if self.board.piece(self.posx + (multiple*dx),self.posy + (multiple*dy)).colour != self.colour:
                            possible_moves_list.append((self.posx + (multiple*dx),self.posy + (multiple*dy)))
                        break
                possible_moves_list.append((self.posx + (multiple*dx),self.posy + (multiple*dy)))
        return possible_moves_list
            
class King(ChessPiece):
    def __init__(self,colour,posx,posy,num,board):
        ChessPiece.__init__(self,colour,posx,posy,"King",num,board,'K')
        #Initialisation, along with the original_pos attribute to ensure the King hasn't moved before attempting to castle
        self.original_pos = True
        
    def move(self,x,y,is_player_move = True):
        if abs(self.posx-x) != 2: #If abs(self.posx-x) i.e. a move 2 in the x direction either side, it's a castling move
            if (x,y) in self.possible_moves():
                if is_player_move:
                    if self.board.piece(x,y) != None:
                        self.board.move_buffer = 'K' + self.board.square_id(self.posx,self.posy) + 'x' + self.board.square_id(x,y)
                    else:
                        self.board.move_buffer = 'K' + self.board.square_id(self.posx,self.posy) + '-' + self.board.square_id(x,y)
                self.original_pos = False
                return self.piece_move(x,y)
            return False
        else:
            #If equal to 2 in x, its a castle
            if (x,y) in self.castling_moves():
                if x < self.posx: #Queenside
                    self.board.move_buffer = '0-0-0'
                    self.board.piece(0,y).piece_move(self.posx-1,y)
                else: #Kingside
                    self.board.move_buffer = '0-0'
                    self.board.piece(7,y).piece_move(self.posx+1,y)
                self.original_pos = False
                return self.piece_move(x,y)
            return False
        
    def possible_moves(self):
        possible_moves_list = []
        for vector in [(1,1),(1,0),(1,-1),(0,1),(0,-1),(-1,1),(-1,0),(-1,-1)]:
            if 0<=self.posx+vector[0] and 7>=self.posx+vector[0] and 0<=self.posy+vector[1] and 7>=self.posy+vector[1]:
                if self.board.piece(self.posx+vector[0],self.posy+vector[1]) != None:
                    if self.board.piece(self.posx+vector[0],self.posy+vector[1]).colour != self.colour:    
                        possible_moves_list.append((self.posx+vector[0],self.posy+vector[1]))
                else:
                    possible_moves_list.append((self.posx+vector[0],self.posy+vector[1]))
        return possible_moves_list
    
    def castling_moves(self):
        possible_moves_list = []
        self.board.check_checkspaces()
        if self.original_pos and not((self.colour == 1 and (self.posx,self.posy) in self.board.checkspaces_white) or (self.colour == -1 and (self.posx,self.posy) in self.board.checkspaces_black)):
            #Kingside Castling
            if (self.board.piece(self.posx+1,self.posy) == None) and not((self.colour == 1 and (self.posx+1,self.posy) in self.board.checkspaces_white) or (self.colour == -1 and (self.posx+1,self.posy) in self.board.checkspaces_black)):
                if (self.board.piece(self.posx+2,self.posy) == None) and not((self.colour == 1 and (self.posx+2,self.posy) in self.board.checkspaces_white) or (self.colour == -1 and (self.posx+2,self.posy) in self.board.checkspaces_black)):
                    if type(self.board.piece(7,self.posy)) == Rook:
                        if self.board.piece(7,self.posy).original_pos:
                            possible_moves_list.append((self.posx+2,self.posy))
            #Queenside Castling
            if (self.board.piece(self.posx-1,self.posy) == None) and not((self.colour == 1 and (self.posx-1,self.posy) in self.board.checkspaces_white) or (self.colour == -1 and (self.posx-1,self.posy) in self.board.checkspaces_black)):
                if (self.board.piece(self.posx-2,self.posy) == None) and not((self.colour == 1 and (self.posx-2,self.posy) in self.board.checkspaces_white) or (self.colour == -1 and (self.posx-2,self.posy) in self.board.checkspaces_black)):
                    if (self.board.piece(self.posx-3,self.posy) == None) and not((self.colour == 1 and (self.posx-3,self.posy) in self.board.checkspaces_white) or (self.colour == -1 and (self.posx-3,self.posy) in self.board.checkspaces_black)):
                        if type(self.board.piece(0,self.posy)) == Rook:
                            if self.board.piece(0,self.posy).original_pos:
                                possible_moves_list.append((self.posx-2,self.posy))
        return possible_moves_list

#Used by check_checkmate() method and AI class to describe moves which can then be run
class MoveObject:
    def __init__(self,identifier,posx,posy,to_tuple,promotion = 0,score = 0):
        self.identifier = identifier
        self.from_x = posx
        self.from_y = posy
        self.to_x = to_tuple[0]
        self.to_y = to_tuple[1]
        self.promotion = promotion #Only not zero when used by AI
        
    def execute(self,board,is_checkmate_search):
        move_success = (board.pieces[self.identifier]).move(self.to_x,self.to_y,not is_checkmate_search) #If its a checkmate search, it's not a player move
        if move_success and self.promotion != 0:
            board.promote(board.pieces[self.identifier],self.promotion)
        return move_success

##### AI ######

#Zobrist hash initialisation
zobrist_table = [[[[random.randint(1,2**64 - 1) for i in range(0,8)] for j in range(0,8)] for k in range(0,6)] for l in range(0,2)]
zobrist_list= [random.randint(1,2**64 - 1) for a in range(0,13)]

#Subclass of board is used, as the turn_increment method of the typical board representation contains redundancies for an AI
class AIboard(Board):
    def increment_turn(self):
        if not self.check_check(): #If in a check position after turn is made, invalid move
            self.current_index += 1
            self.record_board(self.current_index)
            self.revert_board(self.current_index)
            for piece in self.pieces:
                if piece.colour == self.turn and type(piece) == Pawn:
                    piece.double_move = False
            return True
        else:
            self.revert_board(self.current_index)
            return False

class AI:
    def __init__(self,depth,colour):
        self.max_depth = depth
        self.colour = colour
        #Piece-square tables are taken from https://www.chessprogramming.org/Simplified_Evaluation_Function
        self.pawn_piece_table = [[100, 100, 100, 100, 100, 100, 100, 100],
                                 [150, 150, 150, 150, 150, 150, 150, 150],
                                 [110, 110, 120, 130, 130, 120, 110, 110],
                                 [105, 105, 110, 125, 125, 110, 105, 105],
                                 [100, 100, 100, 120, 120, 100, 100, 100],
                                 [105, 95, 90, 100, 100, 90, 95, 105],
                                 [105, 110, 110, 80, 80, 110, 110, 105],
                                 [100, 100, 100, 100, 100, 100, 100, 100]]
        self.knight_piece_table = [[270, 280, 290, 290, 290, 290, 280, 270],
                                   [280, 300, 320, 320, 320, 320, 300, 280],
                                   [290, 320, 330, 335, 335, 330, 320, 290],
                                   [290, 325, 335, 340, 340, 335, 325, 290],
                                   [290, 320, 335, 340, 340, 335, 320, 290],
                                   [290, 325, 330, 335, 335, 330, 325, 290],
                                   [280, 300, 320, 325, 325, 320, 300, 280],
                                   [270, 280, 290, 290, 290, 290, 280, 270]]
        self.bishop_piece_table = [[310, 320, 320, 320, 320, 320, 320, 310],
                                   [320, 330, 330, 330, 330, 330, 330, 320],
                                   [320, 330, 335, 340, 340, 335, 330, 320],
                                   [320, 335, 335, 340, 340, 335, 335, 320],
                                   [320, 330, 340, 340, 340, 340, 330, 320],
                                   [320, 340, 340, 340, 340, 340, 340, 320],
                                   [320, 335, 330, 330, 330, 330, 335, 320],
                                   [310, 320, 320, 320, 320, 320, 320, 310]]
        self.rook_piece_table = [[500, 500, 500, 500, 500, 500, 500, 500],
                                 [505, 510, 510, 510, 510, 510, 510, 505],
                                 [495, 500, 500, 500, 500, 500, 500, 495],
                                 [495, 500, 500, 500, 500, 500, 500, 495],
                                 [495, 500, 500, 500, 500, 500, 500, 495],
                                 [495, 500, 500, 500, 500, 500, 500, 495],
                                 [495, 500, 500, 500, 500, 500, 500, 495],
                                 [500, 500, 500, 505, 505, 500, 500, 500]]
        self.queen_piece_table = [[880, 890, 890, 895, 895, 890, 890, 880],
                                  [890, 900, 900, 900, 900, 900, 900, 890],
                                  [890, 900, 905, 905, 905, 905, 900, 890],
                                  [895, 900, 905, 905, 905, 905, 900, 895],
                                  [900, 900, 905, 905, 905, 905, 900, 895],
                                  [890, 905, 905, 905, 905, 905, 900, 890],
                                  [890, 900, 905, 900, 900, 900, 900, 890],
                                  [880, 890, 890, 895, 895, 890, 890, 880]]
        self.piece_square_tables = {Pawn:self.pawn_piece_table,Knight:self.knight_piece_table,Bishop:self.bishop_piece_table,Rook:self.rook_piece_table,Queen:self.queen_piece_table}
        self.king_mid_piece_table = [[19970, 19960, 19960, 19950, 19950, 19960, 19960, 19970],
                                     [19970, 19960, 19960, 19950, 19950, 19960, 19960, 19970],
                                     [19970, 19960, 19960, 19950, 19950, 19960, 19960, 19970],
                                     [19970, 19960, 19960, 19950, 19950, 19960, 19960, 19970],
                                     [19980, 19970, 19970, 19960, 19960, 19970, 19970, 19980],
                                     [19990, 19980, 19980, 19980, 19980, 19980, 19980, 19990],
                                     [20020, 20020, 20000, 20000, 20000, 20000, 20020, 20020],
                                     [20020, 20030, 20010, 20000, 20000, 20010, 20030, 20020]]
        self.king_end_piece_table = [[19950, 19960, 19970, 19980, 19980, 19970, 19960, 19950],
                                     [19970, 19980, 19990, 20000, 20000, 19990, 19980, 19970],
                                     [19970, 19990, 20020, 20030, 20030, 20020, 19990, 19970],
                                     [19970, 19990, 20030, 20040, 20040, 20030, 19990, 19970],
                                     [19970, 19990, 20030, 20040, 20040, 20030, 19990, 19970],
                                     [19970, 19990, 20020, 20030, 20030, 20020, 19990, 19970],
                                     [19970, 19970, 20000, 20000, 20000, 20000, 19970, 19970],
                                     [19950, 19970, 19970, 19970, 19970, 19970, 19970, 19950]]
        self.hash_table = {}
    
    def zobrist_hash(self):
        hashval = 0
        #Piece type to the index in the zobrist table
        piece_to_index = {Pawn:0,Knight:1,Bishop:2,Rook:3,Queen:4,King:5}
        #If turn is white
        if self.ai_board.turn == 1:
            hashval ^= zobrist_list[0]
        #Cycles through pieces
        for piece in self.ai_board.pieces:
            if piece.alive:
                if piece.colour == 1:
                    hashval ^= zobrist_table[0][piece_to_index[type(piece)]][piece.posx][piece.posy]
                else:
                    hashval ^= zobrist_table[1][piece_to_index[type(piece)]][piece.posx][piece.posy]
                if type(piece) == Pawn:
                    #For en passant ranks
                    if piece.double_move:
                        hashval ^= zobrist_list[5+piece.posx]
        #Castling rights
        if self.ai_board.white_king.original_pos:
            if type(self.ai_board.piece(7,7)) == Rook:
                if self.ai_board.piece(7,7).original_pos:
                    hashval ^= zobrist_list[1]
            elif type(self.ai_board.piece(0,7)) == Rook:
                if self.ai_board.piece(0,7).original_pos:
                    hashval ^= zobrist_list[2]
        if self.ai_board.black_king.original_pos:
            if type(self.ai_board.piece(7,0)) == Rook:
                if self.ai_board.piece(7,0).original_pos:
                    hashval ^= zobrist_list[3]
            elif type(self.ai_board.piece(0,0)) == Rook:
                if self.ai_board.piece(0,0).original_pos:
                    hashval ^= zobrist_list[4]
        return hashval

    def generate_move_list(self,colour): #Used to check for checkmate and used in AI
        moves = []
        for piece in self.ai_board.pieces:
            if piece.colour == colour and piece.alive:
                if type(piece) == Pawn: #For pawns moving to the final rank, a promotion index is needed
                    for move in piece.possible_moves():
                        if piece.colour == -1 and move[1] == 7:
                            for index in range(1,5):
                                moves.append(MoveObject(piece.identifier,piece.posx,piece.posy,move,promotion = index))
                        elif piece.colour == 1 and move[1] == 0:
                            for index in range(1,5):
                                moves.append(MoveObject(piece.identifier,piece.posx,piece.posy,move,promotion = index))
                        else:
                            moves.append(MoveObject(piece.identifier,piece.posx,piece.posy,move))
                else:
                    for move in piece.possible_moves():
                        moves.append(MoveObject(piece.identifier,piece.posx,piece.posy,move))
                    if type(piece) == King: #Castling moves needs to be added as isn't part of possible_moves()
                        for move in piece.castling_moves():
                            moves.append(MoveObject(piece.identifier,piece.posx,piece.posy,move))
        return moves
    
    def minimax_root(self,boardclass):
        s = time.time()
        depth = 0
        #set alpha and beta for pruning
        alpha = -20000
        beta = 20000
        best_value = -20001
        #initialises AI copy of board
        self.ai_board = AIboard(self.colour)
        self.ai_board.record_of_boards = [boardclass.record_of_boards[-1]]
        self.ai_board.turn = self.colour
        self.ai_board.revert_board(0)
        #Generates a list of moves to iterate through
        moves = self.generate_move_list(self.ai_board.turn)
        ordered_moves = []
        for move in moves:
            move.execute(self.ai_board,False)
            if self.ai_board.increment_turn():
                returned_value = self.evaluate_board()
                #Insert move into ordered_moves based on score
                for index,item in enumerate(ordered_moves):
                    if item[1] < returned_value:
                        ordered_moves.insert(index+1,(move,returned_value))
                        break
                if not (move,returned_value) in ordered_moves:
                    ordered_moves.append((move,returned_value))
            self.ai_board.revert_board(depth)
        moves = []
        for move_score_tuple in ordered_moves:
            moves.append(move_score_tuple[0])
        #Cycles through moves to search through move tree
        for move in moves:
            move.execute(self.ai_board,False)
            if self.ai_board.increment_turn():
                returned_value = self.minimax_node(depth+1,alpha,beta,False)
                if alpha < returned_value: #New move was better
                    optimal_move = move
                    alpha = returned_value
            self.ai_board.revert_board(0)
        #Saves information to transposition table in case board state is searched
        hashval = self.zobrist_hash()
        self.hash_table[hashval] = (alpha,self.max_depth - depth)
        return optimal_move
    
    def minimax_node(self,depth,alpha,beta,is_maximising_node):
        hashval = self.zobrist_hash()
        if hashval in self.hash_table: #Checks if current board has already been evaluated in a previous search
            table_contents = self.hash_table[hashval]
            depth_of_val = table_contents[1]
            table_heuristic_val = table_contents[0]
            if depth_of_val >= self.max_depth - depth: #If stored value is propagated from required depth or deeper
                return table_heuristic_val
        if depth < self.max_depth:
            moves = self.generate_move_list(self.ai_board.turn)
            #Shallow search move ordering
            if self.max_depth - depth > 1: #If remaining depth is one, shallow search depth is the same as required depth
                ordered_moves = []
                for move in moves:
                    move.execute(self.ai_board,False)
                    if self.ai_board.increment_turn():
                        returned_value = self.evaluate_board()
                        #Insert move into ordered_moves based on score
                        for index,item in enumerate(ordered_moves):
                            if item[1] < returned_value:
                                ordered_moves.insert(index+1,(move,returned_value))
                                break
                        if not (move,returned_value) in ordered_moves:
                            ordered_moves.append((move,returned_value))
                    self.ai_board.revert_board(depth)
                moves = []
                for move_score_tuple in ordered_moves:
                    moves.append(move_score_tuple[0])
                    
            if is_maximising_node:
                alpha = -20001
                #Searches through the ordered moves list using minimax
                for move in moves:
                    move_done = move.execute(self.ai_board,False)
                    if self.ai_board.increment_turn():
                        returned_value = self.minimax_node(depth+1,alpha,beta,not is_maximising_node)
                        alpha = max(returned_value,alpha)
                        if alpha >= beta:
                            return alpha
                    self.ai_board.revert_board(depth)
                self.hash_table[hashval] = (alpha,self.max_depth - depth)
                return alpha
            else:
                moves.reverse() #Lowest to highest score, since at a minimising node
                beta = 20001
                for move in moves:
                    move_done = move.execute(self.ai_board,False)
                    if self.ai_board.increment_turn():
                        returned_value = self.minimax_node(depth+1,alpha,beta,not is_maximising_node)
                        beta = min(returned_value,beta)
                        if alpha >= beta:
                            return beta
                    self.ai_board.revert_board(depth)
                self.hash_table[hashval] = (beta,self.max_depth - depth)
                return beta
        else:
            heuristic_val = self.evaluate_board()
            self.hash_table[hashval] = (heuristic_val,0)
            return heuristic_val

    def evaluate_board(self):
        score = 0
        is_endgame = self.check_endgame()
        #Cycles through all the pieces and retrieves values from the tables.
        for piece in self.ai_board.pieces:
            if piece.alive:
                piece_type = type(piece)
                if piece.colour == 1:
                    posx = piece.posx
                    posy = piece.posy
                else:
                    posx = piece.posx
                    posy = 7 - piece.posy
                if piece_type != King:
                    piece_score = (self.piece_square_tables[piece_type][posy][posx])
                else:
                    #Endgame is checked as king utilisation in attacking increases in the endgame.
                    if is_endgame: 
                        piece_score = (self.king_end_piece_table[posy][posx])
                    else:
                        piece_score = (self.king_mid_piece_table[posy][posx])
                #Accumulates the score
                if piece.colour == self.colour:
                    score += piece_score
                else:
                    score -= piece_score
        return score
    
    def check_endgame(self):
        #Coutns material in terms of piece and colour
        material = {(Pawn,-1):0,(Knight,-1):0,(Bishop,-1):0,(Rook,-1):0,(Queen,-1):0,(King,-1):0,(Pawn,1):0,(Knight,1):0,(Bishop,1):0,(Rook,1):0,(Queen,1):0,(King,1):0}
        for piece in self.ai_board.pieces:
            if piece.alive:
                material[(type(piece),piece.colour)] += 1
        black_minor_piece_count = material[(Knight,-1)] + material[(Bishop,-1)] + material[(Rook,-1)]
        white_minor_piece_count = material[(Knight,1)] + material[(Bishop,1)] + material[(Rook,1)]
        #No queen or a queen and at most one minor piece for each side
        return (material[(Queen,-1)] == 0 or black_minor_piece_count <= 1) and (material[(Queen,1)] or white_minor_piece_count <= 1)

##### INTERFACE #####

### Game display classes
    
class PygameButton:
    def __init__(self,display,position,imagepath):
        self.image = pygame.image.load(imagepath)
        self.rect = pygame.Rect(position,self.image.get_size())
        self.position = position
        self.display = display

    def draw(self):
        self.display.blit(self.image,self.position)

    def check_clicked(self,event):
        #Checks for event_type == pygame.MOUSEBUTTONDOWN already done before this function will be called
        if self.rect.collidepoint(event.pos):
            self.click_function()

class Arrow(PygameButton):
    def __init__(self,interface,position,direction,increment):
        imagepath = "Textures/Arrow" + direction + ".png"
        PygameButton.__init__(self,interface.game_display,position,imagepath)
        self.direction = direction
        self.interface = interface #Class assignement, so reference is saved. Any changes to the "local" copy affects the interface copy
        self.increment = increment #increment of two is used against an AI
        
    def click_function(self):
        if self.direction == "Left":
            if self.interface.chess_board.current_index-self.increment >= 0: #Checks if user is not going back further than possible
                self.interface.chess_board.revert_board(self.interface.chess_board.current_index-self.increment)
                self.interface.update_displayed_pieces()
                self.interface.update_move_list()
                return True
            else:
                return False
        elif self.direction == "Right": #Checks if user is not going past the newest board state
            if self.interface.chess_board.current_index+self.increment <= len(self.interface.chess_board.record_of_boards)-1:
                self.interface.chess_board.revert_board(self.interface.chess_board.current_index+self.increment)
                self.interface.update_displayed_pieces()
                self.interface.update_move_list()
                return True
            else:
                return False
        
class ExitButton(PygameButton):
    def __init__(self,interface,position):
        imagepath = "Textures/ExitButton.png"
        PygameButton.__init__(self,interface.game_display,position,imagepath)
        self.interface = interface

    def click_function(self):
        #Ask to be sure
        self.interface.exit_button_pressed = True
        self.interface.exit_game = True

class GameInterface:
    def __init__(self,is_playable,AI_player = False,AI_colour = -1,game_file = None): #game_file with .json extension
        pygame.init()
        #Sets display up and variables needed for display
        self.chess_board = Board(1)
        self.game_display = pygame.display.set_mode((900,600))
        pygame.display.set_caption("Chess")
        self.is_playable = is_playable #Is False when looking at historical game
        self.selected_piece = None
        if not self.is_playable: #If not playable, the application is loading a game
            self.chess_board.load_game_to_board(game_file)
        self.displayed_pieces = []
        self.moves_to_display = list() #Moves of the score sheet that are displayed on the interface peripherals
        self.update_displayed_pieces()
        self.orientation = AI_colour * -1 #Facing against the AI always, whether black or white. Default, white POV first
        self.exit_game = False #Used to determine to exit a game, whether by end game state or user exit
        self.exit_button_pressed = False #Whether game has been ended using the exit button
        self.buttons = []
        if AI_player:
            self.game_AI = AI(3,AI_colour)
            self.buttons.append(Arrow(self,(615,20),"Left",2))
            self.buttons.append(Arrow(self,(690,20),"Right",2))
        else:
            self.game_AI = None
            self.buttons.append(Arrow(self,(615,20),"Left",1))
            self.buttons.append(Arrow(self,(690,20),"Right",1))
        self.buttons.append(ExitButton(self,(770,20)))
        self.move_font = pygame.font.SysFont('couriernew',16)
        self.prompt_font = pygame.font.SysFont('arial',20)
        self.prompt = None
        self.square_width = 75 #Constant used to determine the position of the mouse on the board
        
    def update_display(self):
        ###Updates display
        #Clears the board
        self.game_display.fill((60,60,60))
        #Displays the chess_board image and buttons
        self.game_display.blit(self.chess_board.image,(0,0))
        for button in self.buttons:
            button.draw()
        #Displays prompt
        self.display_prompt()
        #Displays move list
        self.display_move_list()
        #Displays each individual piece, while considering the self.orientation
        for piece in self.displayed_pieces:
            if self.orientation == 1:
                self.game_display.blit(piece.image,(piece.posx*self.square_width+7,piece.posy*self.square_width+7))
            else:
                self.game_display.blit(piece.image,(532-(piece.posx*self.square_width),532-(piece.posy*self.square_width)))
        #Displays the self.selected_piece to be directly on the mouse
        if self.selected_piece != None:
            x,y = pygame.mouse.get_pos()
            self.game_display.blit(self.selected_piece.image,(x-30,y-27))
        #The image created using the algorithm above is displayed on the screen
        pygame.display.update()

    def display_prompt(self):
        if self.prompt != None:
            text = self.prompt_font.render(self.prompt,True,(0,0,0),(255,0,0))
            text_rect = text.get_rect()
            text_rect.top = 160
            text_rect.left = 630
            self.game_display.blit(text,text_rect)

    def update_move_list(self):
        move_display_count = 20 #Max moves that can be displayed at once
        if self.chess_board.current_index == 0: #Reverted to original board state
            self.moves_to_display = self.chess_board.list_of_moves[0:move_display_count]
            self.first_displayed_move_index = 0
        elif len(self.chess_board.list_of_moves) > move_display_count: #more than can be displayed at once
            rows_for_all_moves = (len(self.chess_board.list_of_moves)+1)//2 #Number of rows an extensive score sheet of the game would need
            row_of_current_move = (self.chess_board.current_index+1)//2 #Row of move previous to the current board state being displayed
            if row_of_current_move <= rows_for_all_moves - round(move_display_count/2): #If current move is not recent enough  
                if (self.chess_board.current_index - 1) % 2 == 0: #White turn, as white move must be displayed in the top left
                    self.moves_to_display = self.chess_board.list_of_moves[self.chess_board.current_index - 1:self.chess_board.current_index + move_display_count - 1]
                    self.first_displayed_move_index = self.chess_board.current_index - 1
                else:
                    self.moves_to_display = self.chess_board.list_of_moves[self.chess_board.current_index - 2:self.chess_board.current_index + move_display_count - 2]
                    self.first_displayed_move_index = self.chess_board.current_index - 2
            else:
                if (len(self.chess_board.list_of_moves) - 1) % 2 == 0: #White turn
                    self.moves_to_display = self.chess_board.list_of_moves[-move_display_count + 1:]
                    self.first_displayed_move_index = len(self.chess_board.list_of_moves) - move_display_count + 1
                else:
                    self.moves_to_display = self.chess_board.list_of_moves[-move_display_count:]
                    self.first_displayed_move_index = len(self.chess_board.list_of_moves) - move_display_count
        else:
            self.moves_to_display = self.chess_board.list_of_moves
            self.first_displayed_move_index = 0
        #moves to display is list of moves that will be visible to the user
        #starting index is the move index of the top left move displayed (i.e. the first move displayed)
            
    def display_move_list(self):
        for index in range(0,len(self.moves_to_display)):
            move = self.moves_to_display[index]
            move_index = self.first_displayed_move_index + index
            if self.chess_board.current_index - 1 == move_index:
                background = (0,0,255) #Blue
            else:
                background = None #No background
            if index % 2 == 0: #White move
                #move number display
                text = self.move_font.render(str(int(move_index/2) + 1) + '. ',True,(255,255,255),None)
                text_rect = text.get_rect()
                text_rect.top = 220 + ((index) * 10)
                text_rect.left = 630
                self.game_display.blit(text,text_rect)
                #White move
                text = self.move_font.render(move,True,(255,255,255),background)
                text_rect = text.get_rect()
                text_rect.top = 220 + ((index) * 10)
                text_rect.left = 660
            else: #Black move
                text = self.move_font.render(move,True,(255,255,255),background)
                text_rect = text.get_rect()
                text_rect.top = 220 + ((index-1) * 10)
                text_rect.left = 745
            self.game_display.blit(text,text_rect)

    def update_displayed_pieces(self):
        self.displayed_pieces = []
        for piece in self.chess_board.pieces:
            if piece.alive:
                self.displayed_pieces.append(piece)
                
    def mainloop(self):
        move_done = False
        move_tried = False
        self.update_move_list()
        while not self.exit_game:
            self.update_display()
            if self.game_AI != None:
                if self.game_AI.colour == self.chess_board.turn:
                    AImove = self.game_AI.minimax_root(self.chess_board)
                    AImove.execute(self.chess_board,False)
                    self.chess_board.increment_turn()
                    self.update_displayed_pieces()
                    self.update_move_list()
                    self.update_display()
                    #Wait a bit to make the turn switch less jarring for the user
                    if self.chess_board.endstate != 0:
                        self.end_game()
                        return
            for event in pygame.event.get(): #Checks all events that have occurred since last checked
                if event.type == pygame.MOUSEBUTTONDOWN:
                    if event.button == 1: #Checks for left click
                        for button in self.buttons:
                            button.check_clicked(event)
                        if self.is_playable: #Piece clicks are ignored when attribute is false
                            x,y = event.pos
                            if self.orientation == 1:#White POV
                                if x//self.square_width <= 7 and x//self.square_width >=0 and y//self.square_width <= 7 and y//self.square_width >= 0:
                                    self.selected_piece = self.chess_board.piece(x//self.square_width,y//self.square_width)
                            else: #Black BOV (self.orientation == -1)
                                if 7-x//self.square_width <= 7 and 7-x//self.square_width >=0 and 7-y//self.square_width <= 7 and 7-y//self.square_width >= 0:
                                    self.selected_piece = self.chess_board.piece(7-x//self.square_width,7-y//self.square_width)
                            #If the square that was clicked on wasn't empty, and if it's the piece's colour's turn, the piece is removed from the list of pieces (so it isn't displayed in that place, hence it can follow the mouse)
                            if self.selected_piece != None:
                                if self.selected_piece.colour == self.chess_board.turn:
                                    self.displayed_pieces.remove(self.selected_piece)
                                    #Removed so that it isn't displayed in old position while being moved as blit below uses list of pieces
                                else:
                                    self.selected_piece = None
                                
                #Checks if the left click is released
                elif event.type == pygame.MOUSEBUTTONUP and self.is_playable:
                    if event.button == 1:
                        #If there was a piece selected, the square the mouse was over is calculated using the x, y and self.orientation of the board, and is added back into the list of pieces so it can be displayed on that space
                        if self.selected_piece != None:
                            self.displayed_pieces.append(self.selected_piece)
                            x,y = event.pos
                            #The move_done variable holds whether the move was successful (True) or not (False)
                            if self.orientation == 1:#White POV
                                if x//self.square_width <= 7 and x//self.square_width >=0 and y//self.square_width <= 7 and y//self.square_width >= 0:
                                    boardx = x//self.square_width
                                    boardy = y//self.square_width
                                    move_tried = True
                                    move_done = self.selected_piece.move(boardx,boardy)
                            else: #Black BOV (self.orientation == -1)
                                if 7-x//self.square_width <= 7 and 7-x//self.square_width >=0 and 7-y//self.square_width <= 7 and 7-y//self.square_width >= 0:
                                    boardx = 7-x//self.square_width
                                    boardy = 7-y//self.square_width
                                    move_tried = True
                                    move_done = self.selected_piece.move(boardx,boardy)
                                    
                            #In case the move calls for promotion, the type of piece is checked
                            if type(self.selected_piece) == Pawn and move_done:
                                #Checks if the pawn is at the opposite end of the board of the colours starting side indicating a promotion
                                if (self.chess_board.turn == -1 and boardy == 7) or (self.chess_board.turn == 1 and boardy == 0):
                                    dialogue_box = tkinter.Tk() #Initialises dialogue box
                                    dialogue_box.title("PROMOTION")
                                    tkinter.Label(master = dialogue_box,text = "Promote pawn to:").pack()
                                    user_input = tkinter.IntVar() #Declares the variable to store the user input
                                    for number,piece in enumerate(["Queen","Rook","Bishop","Knight"]): #Adds Radiobuttons (only one can be selected) to the dialogue box
                                        tkinter.Radiobutton(master = dialogue_box,text = piece,variable = user_input,value = number).pack(anchor = tkinter.W,padx = 80)
                                    tkinter.Button(master = dialogue_box,text = "Promote", command = dialogue_box.destroy).pack()
                                    dialogue_box.geometry("250x150")
                                    dialogue_box.mainloop()
                                    PromotionPiece = user_input.get() #Uses the user_input variable as a list index to choose the piece
                                    self.chess_board.promote(self.selected_piece,PromotionPiece + 1) #add 1 since 0 value used for demotions in board reversions
                            self.selected_piece = None
                #When the game is quit (the x button is pressed
                elif event.type == pygame.QUIT:
                    pygame.quit()
                    quit()
                #When F is pressed to flip the board
                elif event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_f:
                        self.orientation *= -1
                        
            #Check if the move has been taken properly (i.e. not moved into check, or still in check after a move)
            #If move_done is false, this block will be completely ignored, therefore no change will have occured to any variables (the attributes of the piece are only changed if move_done is True)
            if move_done:
                if self.chess_board.increment_turn():
                    #move_done is changed back to False
                    move_done = False
                    move_tried = False
                    self.update_displayed_pieces()
                    self.update_move_list()
                    self.update_display()
                    #Wait a bit to make the turn switch less jarring for the user
                    time.sleep(0.15)
                    if self.chess_board.endstate != 0:
                        self.exit_game = True
                    if self.chess_board.endstate == 0 and self.game_AI == None:
                        self.orientation *= -1
                    self.prompt = None
                else: #In this case, king was moved into, or remained in Check after the move
                    if self.chess_board.in_check:
                        self.prompt = "You must move out of check!"
                        #Display still in check
                    else:
                        self.prompt = "You can't move into check!"
                        #Display must move out of check
                    move_done = False
                    move_tried = False
            elif move_tried: #In this case, chosen move was not in range of possible moves for the piece
                self.prompt = "Invalid move, try another move"
                move_tried = False
                #Display invalid move
        self.end_game()
        return
                
    def end_game(self):
        #When the loop is broken, depending on who won the game a pop up is shown to indicate who has won or it'll show that the game has reached a stalemate
        if self.is_playable:
            self.game_end_display = tkinter.Tk()
            if self.exit_button_pressed: #Exit button
                self.game_end_display.title("DRAW")
                tkinter.Label(self.game_end_display,text = "Game was quit").grid(row = 0,columnspan = 2,pady = 10)
            else:
                if self.chess_board.endstate == 3: #Insufficient material
                    self.game_end_display.title("DRAW")
                    tkinter.Label(self.game_end_display,text = "Draw by insufficient material").grid(row = 0,columnspan = 2,pady = 10)
                if self.chess_board.endstate == 2: #Stalemate
                    self.game_end_display.title("DRAW")
                    tkinter.Label(self.game_end_display,text = "Draw by stalemate").grid(row = 0,columnspan = 2,pady = 10)
                elif self.chess_board.endstate == 1: #White checkmate
                    self.game_end_display.title("CHECKMATE")
                    tkinter.Label(self.game_end_display,text = "White Win by checkmate").grid(row = 0,columnspan = 2,pady = 10)
                elif self.chess_board.endstate == -1: #Black checkmate
                    self.game_end_display.title("CHECKMATE")
                    tkinter.Label(self.game_end_display,text = "Black wins by checkmate").grid(row = 0,columnspan = 2,pady = 10)
            tkinter.Button(self.game_end_display,text = "Save game",command = self.save_game).grid(row = 1,column = 0,pady = 10,padx = 20)
            tkinter.Button(self.game_end_display,text = "Exit game",command = self.game_end_display.destroy).grid(row = 1,column = 1,pady = 10,padx = 20)
            self.game_end_display.mainloop()
        #Quits the game
        pygame.quit()
    
    def save_game(self):
        self.game_end_display.destroy()
        self.game_name_prompt = tkinter.Tk()
        self.game_name_prompt.title("SAVE GAME")
        tkinter.Label(self.game_name_prompt, text = "Enter name (default is 'Game'):").grid(row = 0,pady = 10,padx = 10)
        self.user_entry = tkinter.Entry(self.game_name_prompt) #Entry point for game name
        self.user_entry.grid(row = 1,pady = 10)
        tkinter.Button(self.game_name_prompt,text = "Confirm",command = self.close_game_name_prompt).grid(row = 2,pady = 10) #destroys prompt box, allow the function to continue execution, locking in the name entered by the user
        self.game_name_prompt.mainloop()

    def close_game_name_prompt(self):
        game_name = self.user_entry.get()
        if game_name == "":
            game_name = "Game"
        self.chess_board.save_game(game_name)
        self.game_name_prompt.destroy()

### Load game menu

class LoadInterface:
    def __init__(self):
        self.pageno = 0
        self.pages = []
        self.close = False

    def create_menu(self):
        self.menu = tkinter.Tk()
        self.menu.title("LOAD GAME")
        self.menu.protocol("WM_DELETE_WINDOW",exit) #The 'X' button is overriden with written function such that self.close is changed
        self.update_pages()
        #Game dipslay
        if len(self.pages) != 0: #Checks if there are any games to load
            games = self.pages[self.pageno]
            self.game_frame = tkinter.Frame(self.menu) #Frame containing widgets relating to saved games, seperate from button frame as games need updating
            self.game_frame.grid(row = 0)
            if len(games) != 0:
                for row_count,game in enumerate(games): #row_count is used for the grid row of labels and buttons
                    label_string = game["game_name"] + " \nPlayed: " + game["datetimeplayedstring"]
                    file_name = game["file_name"]
                    single_game_display = tkinter.Frame(self.game_frame) #for a single game display, while game_frame is used for all game file displays
                    single_game_display.grid(row = row_count)
                    tkinter.Label(single_game_display,text = label_string,font = ("Arial", 13),borderwidth = 2,relief = "groove").grid(row = 0,column = 0,pady = 10,padx = 10)
                    tkinter.Button(single_game_display,text = "Load",command = (lambda f = file_name: self.load_game(f))).grid(row = 0,column = 1,ipady = 10,ipadx = 10)
                    tkinter.Button(single_game_display,text = "Delete",command = (lambda f = file_name: self.delete_game(f))).grid(row = 0,column = 2,ipady = 10,ipadx = 10)
                    row_count += 1
            #Page counter
            page_count = "Page " + str(self.pageno + 1) + "/" + str(len(self.pages))
            self.page_display = tkinter.Label(self.menu,text = page_count)
            self.page_display.grid(row = 1)
            #Buttons
            self.button_frame = tkinter.Frame(self.menu)
            self.button_frame.grid(row = 2)
            self.back_button = tkinter.Button(self.button_frame,text = "Go back",command = self.exit_menu)
            self.back_button.grid(row = 0,column = 1,pady = 10,padx = 10)
            self.prev_button = tkinter.Button(self.button_frame,text = "Prev page",command = (lambda: self.change_page(-1)))
            self.prev_button.grid(row = 0,column = 0,pady = 10,padx = 10)
            self.next_button = tkinter.Button(self.button_frame,text = "Next page",command = (lambda: self.change_page(1)))
            self.next_button.grid(row = 0,column = 2,pady = 10,padx = 10)
        else:
            tkinter.Label(self.menu, text = "You have no saved games!").grid(row = 0,column = 0,pady = 10,padx = 10)
            self.back_button = tkinter.Button(self.menu,text = "Go back",command = self.exit_menu)
            self.back_button.grid(row = 1,column = 0,pady = 10,padx = 10)
            

    def exit_menu(self):
        self.close = True
        self.menu.destroy()

    def update_menu(self): #clears and updates games display and page counter
        self.game_frame.destroy()
        games = self.pages[self.pageno]
        self.game_frame = tkinter.Frame(self.menu) #Frame containing widgets relating to saved games, seperate from button frame as games need updating
        self.game_frame.grid(row = 0)
        if len(games) != 0:
            for row_count,game in enumerate(games): #row_count is used for the grid row of labels and buttons
                label_string = game["game_name"] + " \nPlayed: " + game["datetimeplayedstring"]
                file_name = game["file_name"]
                single_game_display = tkinter.Frame(self.game_frame) #for a single game display, while game_frame is used for all game file displays
                single_game_display.grid(row = row_count)
                tkinter.Label(single_game_display,text = label_string,font = ("Arial", 13),borderwidth = 2,relief = "groove").grid(row = 0,column = 0,pady = 10,padx = 10)
                tkinter.Button(single_game_display,text = "Load",command = (lambda f = file_name: self.load_game(f))).grid(row = 0,column = 1,ipady = 10,ipadx = 10)
                tkinter.Button(single_game_display,text = "Delete",command = (lambda f = file_name: self.delete_game(f))).grid(row = 0,column = 2,ipady = 10,ipadx = 10)
                row_count += 1
        page_text = "Page " + str(self.pageno + 1) + "/" + str(len(self.pages))
        self.page_display.config(text = page_text)
        

    def change_page(self,increment):
        if self.pageno + increment < len(self.pages) and self.pageno + increment >= 0:
            self.pageno += increment
        self.update_menu()

    def load_game(self,file_name):
        self.menu.destroy()
        game = GameInterface(False,game_file = file_name)
        game.mainloop()

    def delete_game(self,game):
        os.remove("Games/" + game)
        self.update_pages()
        self.update_menu()

    def mainloop(self):
        while not self.close:
            self.create_menu()
            self.menu.mainloop()

    def get_metadata(self,file_name):
        with open("Games/" + file_name,"r") as loadfile:
            game = json.load(loadfile)
        metadata = {}
        metadata["file_name"] = file_name
        metadata["datetimeplayedstring"] = game["datetimeplayedstring"]
        metadata["datetimeplayedUNIX"] = float(game["datetimeplayedUNIX"])
        metadata["game_name"] = game["game_name"]
        return metadata

    def check_file(self,file_name):
        try:
            with open("Games/" + file_name,"r") as loadfile:
                game = json.load(loadfile)
            for in_game in map(lambda item: item in game,["list_of_moves","record_of_boards","game_name","datetimeplayedstring","datetimeplayedUNIX"]):
                if not in_game:
                    return False
            return True
        except:
            return False

    def update_pages(self):
        self.pages = []
        items_per_page = 5
        if os.path.exists("Games"):
            games_list = []
            for file_name in os.listdir("Games"): #Lists all paths in game dir, directory and file
                if os.path.isfile("Games/" + file_name) and self.check_file(file_name): #Filters out directories and checks if file has the correct format
                    games_list.append(self.get_metadata(file_name))
            ordered_games_list = self.mergesort_games_list(games_list)
            for index in range(0,len(ordered_games_list),items_per_page):
                if index + items_per_page > len(ordered_games_list):
                    self.pages.append(ordered_games_list[index:])
                else:
                    self.pages.append(ordered_games_list[index:index+items_per_page])

    def mergesort_games_list(self,games_list): #Orders list using "datetimeplayedUNIX" key
        if len(games_list) <= 1:
            return games_list
        else:
            sorted_list = []
            midpoint = round(len(games_list)/2)
            left = self.mergesort_games_list(games_list[:midpoint])
            right = self.mergesort_games_list(games_list[midpoint:])
            leftindex = 0
            rightindex = 0
            while leftindex < len(left) and rightindex < len(right):
                if left[leftindex]["datetimeplayedUNIX"] > right[rightindex]["datetimeplayedUNIX"]:
                    sorted_list.append(left[leftindex])
                    leftindex += 1
                elif left[leftindex]["datetimeplayedUNIX"] < right[rightindex]["datetimeplayedUNIX"]:
                    sorted_list.append(right[rightindex])
                    rightindex += 1
                else:
                    sorted_list.append(left[leftindex])
                    leftindex += 1
                    sorted_list.append(right[rightindex])
                    rightindex += 1
            if leftindex < len(left):
                sorted_list += left[leftindex:]
            else:
                sorted_list += right[rightindex:]
            return sorted_list

### Main menu

class MainInterface:
    def __init__(self):
        self.close = False
        self.create_main_menu()
        
    def create_main_menu(self):
        self.main_menu = tkinter.Tk()
        #Redefines the 'x' button function
        self.main_menu.protocol("WM_DELETE_WINDOW",self.exit_app) #The 'X' button is overriden with written function such that self.close is changed
        #Interface displays
        self.main_menu.title("CHESS")
        title = tkinter.Label(self.main_menu,text = "CHESS GAME",font = ("Verdana", 20, 'bold'))
        title.grid(row = 0, columnspan = 5,pady = 10)
        menu_image = ImageTk.PhotoImage(Image.open("Textures/MainMenuImage.png"))
        image_label = tkinter.Label(self.main_menu,image = menu_image)
        image_label.image = menu_image
        image_label.grid(row = 1, columnspan = 5)
        #Interface buttons
        tkinter.Button(self.main_menu,text = "How to use",command = self.how_to_use).grid(row = 2,column = 0,pady = 10)
        tkinter.Button(self.main_menu,text = "Load game",command = self.load_game_menu).grid(row = 2,column = 1,pady = 10)
        tkinter.Button(self.main_menu,text = "Human vs Human",command = self.play_human_game).grid(row = 2,column = 2,pady = 10)
        tkinter.Button(self.main_menu,text = "Human vs AI",command = self.play_ai_game).grid(row = 2,column = 3,pady = 10)
        tkinter.Button(self.main_menu,text = "Exit",command = self.exit_app).grid(row = 2,column = 4,pady = 10)

    def exit_app(self):
        #As to break the while loop
        self.close = True
        self.main_menu.destroy()
        
    def mainloop(self):
        #Loop runs until either the x button is pressed or the exit button on the main is pressed, which updates self.close
        while not self.close:
            self.main_menu.mainloop()
            if not self.close:
                self.create_main_menu()
        exit()

    def how_to_use(self):
        self.main_menu.destroy()
        self.sub_menu = tkinter.Tk()
        self.sub_menu.title("HOW TO USE")
        self.sub_menu.protocol("WM_DELETE_WINDOW",exit)
        tkinter.Label(self.sub_menu,text = "To play a game, click and drag pieces to make a move. \nUse the arrows in the top right hand corner to go back and forth moves.\nIf you want to flip the board, press the 'F' key on your keyboard.").grid(row = 0,column = 0,pady = 10)
        tkinter.Button(self.sub_menu,text = "Go back",command = self.go_back).grid(row = 1,column = 0,pady = 10,padx = 20)
        self.sub_menu.mainloop()
            
    def load_game_menu(self):
        self.main_menu.destroy()
        load_int = LoadInterface()
        load_int.mainloop()
        
    def play_human_game(self):
        self.main_menu.destroy()
        #Sets up the game interface for a human vs human game and runs it
        game = GameInterface(True,AI_player = False)
        game.mainloop()

    def play_ai_game(self):
        self.main_menu.destroy()
        #Opens up a sub menu to choose between playing as white or black
        self.sub_menu = tkinter.Tk()
        self.sub_menu.title("CHOOSE SIDE")
        self.sub_menu.protocol("WM_DELETE_WINDOW",exit)
        tkinter.Label(self.sub_menu,text = "Select which side to play as:").grid(row = 0,columnspan = 3,pady = 10)
        tkinter.Button(self.sub_menu,text = "White",command = (lambda: self.play_ai(-1))).grid(row = 1,column = 0,pady = 10,padx = 20)
        tkinter.Button(self.sub_menu,text = "Black",command = (lambda: self.play_ai(1))).grid(row = 1,column = 1,pady = 10,padx = 20)
        tkinter.Button(self.sub_menu,text = "Go back",command = self.go_back).grid(row = 1,column = 2,pady = 10,padx = 20)
        self.sub_menu.mainloop()

    def go_back(self):
        self.sub_menu.destroy()
        
    def play_ai(self,colour):
        self.sub_menu.destroy()
        #Sets up the game interface to play against an AI
        game = GameInterface(True,AI_player = True,AI_colour = colour)
        game.mainloop()

if __name__ == "__main__":
    interface = MainInterface()
    interface.mainloop()
