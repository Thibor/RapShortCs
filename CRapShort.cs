using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading;

namespace RapShortCs
{
	class CUndo
	{
		public int captured;
		public int hash;
		public int passing;
		public int castle;
		public int move50;
		public int lastCastle;
	}

	class CUci
	{
		public string command;
		public string[] tokens;

		public int GetIndex(string key, int def)
		{
			for (int n = 0; n < tokens.Length; n++)
			{
				if (tokens[n] == key)
				{
					return n + 1;
				}
			}
			return def;
		}

		public int GetInt(string key, int def)
		{
			for (int n = 0; n < tokens.Length - 1; n++)
			{
				if (tokens[n] == key)
				{
					return Int32.Parse(tokens[n + 1]);
				}
			}
			return def;
		}

		public void SetMsg(string msg)
		{
			if ((msg == null) || (msg == ""))
			{
				tokens = new string[0];
				command = "";
			}
			else
			{
				tokens = msg.Split(new[] { ' ', '\t' }, StringSplitOptions.RemoveEmptyEntries);
				command = tokens[0];
			}
		}
	}

	class CReader
	{
		private static Thread inputThread;
		private static AutoResetEvent getInput;
		private static AutoResetEvent gotInput;
		public static string input = "";

		static CReader()
		{
			getInput = new AutoResetEvent(false);
			gotInput = new AutoResetEvent(false);
			inputThread = new Thread(Reader);
			inputThread.IsBackground = true;
			inputThread.Start();
		}

		private static void Reader()
		{
			while (true)
			{
				getInput.WaitOne();
				input = "";
				input = Console.ReadLine();
				getInput.Reset();
				gotInput.Set();
			}
		}

		public static string ReadLine(bool wait)
		{
			getInput.Set();
			if (wait)
				gotInput.WaitOne();
			return input;
		}


	}

	class CChess
	{
		const int piecePawn = 0x01;
		const int pieceKnight = 0x02;
		const int pieceBishop = 0x03;
		const int pieceRook = 0x04;
		const int pieceQueen = 0x05;
		const int pieceKing = 0x06;
		const int colorBlack = 0x08;
		const int colorWhite = 0x10;
		const int colorEmpty = 0x20;
		const int moveflagPassing = 0x02 << 16;
		const int moveflagCastleKing = 0x04 << 16;
		const int moveflagCastleQueen = 0x08 << 16;
		const int moveflagPromotion = 0xf0 << 16;
		const int moveflagPromoteQueen = 0x10 << 16;
		const int moveflagPromoteRook = 0x20 << 16;
		const int moveflagPromoteBishop = 0x40 << 16;
		const int moveflagPromoteKnight = 0x80 << 16;
		const int maskCastle = moveflagCastleKing | moveflagCastleQueen;
		const int maskColor = colorBlack | colorWhite;
		int g_captured = 0;
		int g_castleRights = 0xf;
		int g_depth = 0;
		int g_hash = 0;
		int g_passing = 0;
		public int g_move50 = 0;
		int g_moveNumber = 0;
		int g_totalNodes = 0;
		bool g_inCheck = false;
		int g_timeout = 0;
		int g_depthout = 0;
		int g_nodeout = 0;
		int g_mainDepth = 1;
		bool g_stop = false;
		string g_pv = "";
		string g_scoreFm = "";
		int g_lastCastle = 0;
		bool adjInsufficient = false;
		int adjMobility = 0;
		public int undoIndex = 0;
		int[] arrField = new int[64];
		int[] g_board = new int[256];
		int[,] g_hashBoard = new int[256, 16];
		int[] boardCheck = new int[256];
		int[] boardCastle = new int[256];
		public bool whiteTurn = true;
		int usColor = 0;
		int enColor = 0;
		int bsIn = -1;
		int bsDepth = 0;
		string bsFm = "";
		string bsPv = "";
		int[] bonMaterial = new int[7] { 0, 100, 300, 310, 500, 800, 0xffff };
		int[] arrDirKinght = { 14, -14, 18, -18, 31, -31, 33, -33 };
		int[] arrDirBishop = { 15, -15, 17, -17 };
		int[] arrDirRock = { 1, -1, 16, -16 };
		int[] arrDirQueen = { 1, -1, 15, -15, 16, -16, 17, -17 };
		public static Random random = new Random();
		CUndo[] undoStack = new CUndo[0xfff];
		public Stopwatch stopwatch = Stopwatch.StartNew();

		public CChess()
		{
			g_hash = RAND_32();
			for (int n = 0; n < undoStack.Length; n++)
				undoStack[n] = new CUndo();
			for (int y = 0; y < 8; y++)
				for (int x = 0; x < 8; x++)
					arrField[y * 8 + x] = (y + 4) * 16 + x + 4;
			for (int n = 0; n < 256; n++)
			{
				boardCheck[n] = 0;
				boardCastle[n] = 15;
				g_board[n] = 0;
				for (int p = 0; p < 16; p++)
					g_hashBoard[n, p] = RAND_32();
			}
			int[] arrCastleI = { 68, 72, 75, 180, 184, 187 };
			int[] arrCasteleV = { 7, 3, 11, 13, 12, 14 };
			int[] arrCheckI = { 71, 72, 73, 183, 184, 185 };
			int[] arrCheckV = { colorBlack | moveflagCastleQueen, colorBlack | maskCastle, colorBlack | moveflagCastleKing, colorWhite | moveflagCastleQueen, colorWhite | maskCastle, colorWhite | moveflagCastleKing };
			for (int n = 0; n < 6; n++)
			{
				boardCastle[arrCastleI[n]] = arrCasteleV[n];
				boardCheck[arrCheckI[n]] = arrCheckV[n];
			}
		}

		int RAND_32()
		{
			return random.Next();
		}

		string FormatMove(int move)
		{
			string result = FormatSquare(move & 0xFF) + FormatSquare((move >> 8) & 0xFF);
			if ((move & moveflagPromotion) > 0)
			{
				if ((move & moveflagPromoteQueen) > 0) result += 'q';
				else if ((move & moveflagPromoteRook) > 0) result += 'r';
				else if ((move & moveflagPromoteBishop) > 0) result += 'b';
				else result += 'n';
			}
			return result;
		}

		string FormatSquare(int square)
		{
			char[] arr = { 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h' };
			return arr[(square & 0xf) - 4] + (12 - (square >> 4)).ToString();
		}

		int StrToSquare(string s)
		{
			string fl = "abcdefgh";
			int x = fl.IndexOf(s[0]);
			int y = 12 - Int32.Parse(s[1].ToString());
			return (x + 4) | (y << 4);
		}

		bool IsRepetition()
		{
			for (int n = undoIndex - 4; n >= undoIndex - g_move50; n -= 2)
				if (undoStack[n].hash == g_hash)
				{
					return true;
				}
			return false;
		}

		void GenerateMove(List<int> moves, int fr, int to, bool add, int flag)
		{
			int rank = g_board[to] & 7;
			if ((rank == pieceKing) || (((boardCheck[to] & g_lastCastle) == g_lastCastle) && ((g_lastCastle & maskCastle) > 0)))
				g_inCheck = true;
			else if (add)
				if (rank > 0)
					moves.Add(fr | (to << 8) | flag);
				else
					moves.Insert(0, fr | (to << 8) | flag);
		}

		List<int> GenerateAllMoves(bool wt, bool attack)
		{
			adjMobility = 0;
			g_inCheck = false;
			usColor = wt ? colorWhite : colorBlack;
			enColor = wt ? colorBlack : colorWhite;
			int pieceM = 0;
			int pieceN = 0;
			int pieceB = 0;
			List<int> moves = new List<int>(64);
			for (int n = 0; n < 64; n++)
			{
				int fr = arrField[n];
				int f = g_board[fr];
				if ((f & usColor) > 0) f &= 7;
				else continue;
				adjMobility += bonMaterial[f];
				switch (f)
				{
					case 1:
						pieceM++;
						int del = wt ? -16 : 16;
						int to = fr + del;
						if (((g_board[to] & colorEmpty) > 0) && !attack)
						{
							GeneratePwnMoves(moves, fr, to, true, 0);
							if ((g_board[fr - del - del] == 0) && (g_board[to + del] & colorEmpty) > 0)
								GeneratePwnMoves(moves, fr, to + del, true, 0);
						}
						if ((g_board[to - 1] & enColor) > 0)
							GeneratePwnMoves(moves, fr, to - 1, true, 0);
						else if ((to - 1) == g_passing)
							GeneratePwnMoves(moves, fr, g_passing, true, moveflagPassing);
						else if ((g_board[to - 1] & colorEmpty) > 0)
							GeneratePwnMoves(moves, fr, to - 1, false, 0);
						if ((g_board[to + 1] & enColor) > 0)
							GeneratePwnMoves(moves, fr, to + 1, true, 0);
						else if ((to + 1) == g_passing)
							GeneratePwnMoves(moves, fr, g_passing, true, moveflagPassing);
						else if ((g_board[to + 1] & colorEmpty) > 0)
							GeneratePwnMoves(moves, fr, to + 1, false, 0);
						break;
					case 2:
						pieceN++;
						GenerateUniMoves(moves, attack, fr, arrDirKinght, 1);
						break;
					case 3:
						pieceB++;
						GenerateUniMoves(moves, attack, fr, arrDirBishop, 7);
						break;
					case 4:
						pieceM++;
						GenerateUniMoves(moves, attack, fr, arrDirRock, 7);
						break;
					case 5:
						pieceM++;
						GenerateUniMoves(moves, attack, fr, arrDirQueen, 7);
						break;
					case 6:
						GenerateUniMoves(moves, attack, fr, arrDirQueen, 1);
						int cr = wt ? g_castleRights : g_castleRights >> 2;
						if ((cr & 1) > 0)
							if (((g_board[fr + 1] & colorEmpty) > 0) && ((g_board[fr + 2] & colorEmpty) > 0))
								GenerateMove(moves, fr, fr + 2, true, moveflagCastleKing);
						if ((cr & 2) > 0)
							if (((g_board[fr - 1] & colorEmpty) > 0) && ((g_board[fr - 2] & colorEmpty) > 0) && ((g_board[fr - 3] & colorEmpty) > 0))
								GenerateMove(moves, fr, fr - 2, true, moveflagCastleQueen);
						break;
				}
			}
			adjInsufficient = (pieceM == 0) && (pieceN + (pieceB << 1) < 3);
			return moves;
		}

		void GeneratePwnMoves(List<int> moves, int fr, int to, bool add, int flag)
		{
			int y = to >> 4;
			if (((y == 4) || (y == 11)) && add)
			{
				GenerateMove(moves, fr, to, add, moveflagPromoteQueen);
				GenerateMove(moves, fr, to, add, moveflagPromoteRook);
				GenerateMove(moves, fr, to, add, moveflagPromoteBishop);
				GenerateMove(moves, fr, to, add, moveflagPromoteKnight);
			}
			else
				GenerateMove(moves, fr, to, add, flag);
		}

		void GenerateUniMoves(List<int> moves, bool attack, int fr, int[] dir, int count)
		{
			for (int n = 0; n < dir.Length; n++)
			{
				int to = fr;
				int c = count;
				while (c-- > 0)
				{
					to += dir[n];
					if ((g_board[to] & colorEmpty) > 0)
						GenerateMove(moves, fr, to, !attack, 0);
					else if ((g_board[to] & enColor) > 0)
					{
						GenerateMove(moves, fr, to, true, 0);
						break;
					}
					else
						break;
				}
			}
		}

		public int GetMoveFromString(string moveString)
		{
			List<int> moves = GenerateAllMoves(whiteTurn, false);
			for (int i = 0; i < moves.Count; i++)
			{
				if (FormatMove(moves[i]) == moveString)
					return moves[i];
			}
			return 0;
		}

		public void InitializeFromFen(string fen)
		{
			for (int n = 0; n < 64; n++)
				g_board[arrField[n]] = colorEmpty;
			if (fen == "") fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
			string[] chunks = fen.Split(' ');
			int row = 0;
			int col = 0;
			string pieces = chunks[0];
			for (int i = 0; i < pieces.Length; i++)
			{
				char c = pieces[i];
				if (c == '/')
				{
					row++;
					col = 0;
				}
				else if (c >= '0' && c <= '9')
				{
					for (int j = 0; j < Int32.Parse(c.ToString()); j++)
						col++;
				}
				else
				{
					char b = Char.ToLower(c);
					bool isWhite = b != c;
					int piece = isWhite ? colorWhite : colorBlack;
					int index = (row + 4) * 16 + col + 4;
					switch (b)
					{
						case 'p':
							piece |= piecePawn;
							break;
						case 'b':
							piece |= pieceBishop;
							break;
						case 'n':
							piece |= pieceKnight;
							break;
						case 'r':
							piece |= pieceRook;
							break;
						case 'q':
							piece |= pieceQueen;
							break;
						case 'k':
							piece |= pieceKing;
							break;
					}
					g_board[index] = piece;
					col++;
				}
			}
			whiteTurn = chunks[1] == "w";
			g_castleRights = 0;
			if (chunks[2].IndexOf('K') != -1)
				g_castleRights |= 1;
			if (chunks[2].IndexOf('Q') != -1)
				g_castleRights |= 2;
			if (chunks[2].IndexOf('k') != -1)
				g_castleRights |= 4;
			if (chunks[2].IndexOf('q') != -1)
				g_castleRights |= 8;
			g_passing = 0;
			if (chunks[3].IndexOf('-') == -1)
				g_passing = StrToSquare(chunks[3]);
			g_move50 = 0;
			g_moveNumber = Int32.Parse(chunks[5]);
			if (g_moveNumber > 0) g_moveNumber--;
			g_moveNumber *= 2;
			if (!whiteTurn) g_moveNumber++;
			undoIndex = 0;
		}

		public void MakeMove(int move)
		{
			int fr = move & 0xFF;
			int to = (move >> 8) & 0xFF;
			int flags = move & 0xFF0000;
			int piecefr = g_board[fr];
			int piece = piecefr & 0xf;
			int capi = to;
			g_captured = g_board[to];
			g_lastCastle = (move & maskCastle) | (piecefr & maskColor);
			if ((flags & moveflagCastleKing) > 0)
			{
				g_board[to - 1] = g_board[to + 1];
				g_board[to + 1] = colorEmpty;
			}
			else if ((flags & moveflagCastleQueen) > 0)
			{
				g_board[to + 1] = g_board[to - 2];
				g_board[to - 2] = colorEmpty;
			}
			else if ((flags & moveflagPassing) > 0)
			{
				capi = whiteTurn ? to + 16 : to - 16;
				g_captured = g_board[capi];
				g_board[capi] = colorEmpty;
			}
			CUndo undo = undoStack[undoIndex++];
			undo.captured = g_captured;
			undo.hash = g_hash;
			undo.passing = g_passing;
			undo.castle = g_castleRights;
			undo.move50 = g_move50;
			undo.lastCastle = g_lastCastle;
			g_hash ^= g_hashBoard[fr, piece];
			g_passing = 0;
			if ((g_captured & 0xF) > 0)
				g_move50 = 0;
			else if ((piece & 7) == piecePawn)
			{
				if (to == (fr + 32)) g_passing = (fr + 16);
				if (to == (fr - 32)) g_passing = (fr - 16);
				g_move50 = 0;
			}
			else
				g_move50++;
			if ((flags & moveflagPromotion) > 0)
			{
				int newPiece = piecefr & (~0x7);
				if ((flags & moveflagPromoteKnight) > 0)
					newPiece |= pieceKnight;
				else if ((flags & moveflagPromoteQueen) > 0)
					newPiece |= pieceQueen;
				else if ((flags & moveflagPromoteBishop) > 0)
					newPiece |= pieceBishop;
				else
					newPiece |= pieceRook;
				g_board[to] = newPiece;
				g_hash ^= g_hashBoard[to, newPiece & 7];
			}
			else
			{
				g_board[to] = g_board[fr];
				g_hash ^= g_hashBoard[to, piece];
			}
			g_board[fr] = colorEmpty;
			g_castleRights &= boardCastle[fr] & boardCastle[to];
			whiteTurn ^= true;
			g_moveNumber++;
		}

		void UnmakeMove(int move)
		{
			int fr = move & 0xFF;
			int to = (move >> 8) & 0xFF;
			int flags = move & 0xFF0000;
			int piece = g_board[to];
			int capi = to;
			CUndo undo = undoStack[--undoIndex];
			g_passing = undo.passing;
			g_castleRights = undo.castle;
			g_move50 = undo.move50;
			g_lastCastle = undo.lastCastle;
			g_hash = undo.hash;
			int captured = undo.captured;
			if ((flags & moveflagCastleKing) > 0)
			{
				g_board[to + 1] = g_board[to - 1];
				g_board[to - 1] = colorEmpty;
			}
			else if ((flags & moveflagCastleQueen) > 0)
			{
				g_board[to - 2] = g_board[to + 1];
				g_board[to + 1] = colorEmpty;
			}
			if ((flags & moveflagPromotion) > 0)
			{
				piece = (g_board[to] & (~0x7)) | piecePawn;
				g_board[fr] = piece;
			}
			else g_board[fr] = g_board[to];
			if ((flags & moveflagPassing) > 0)
			{
				capi = whiteTurn ? to - 16 : to + 16;
				g_board[to] = colorEmpty;
			}
			g_board[capi] = captured;
			whiteTurn ^= true;
			g_moveNumber--;
		}

		bool GetStop()
		{
			return ((g_timeout > 0) && (stopwatch.Elapsed.TotalMilliseconds > g_timeout)) || ((g_depthout > 0) && (g_mainDepth > g_depthout)) || ((g_nodeout > 0) && (g_totalNodes > g_nodeout));
		}

		int Quiesce(List<int> mu, int depth, int depthL, int alpha, int beta, int score)
		{
			int myMobility = adjMobility;
			int alphaDe = 0;
			int index = mu.Count;
			string alphaPv = "";
			if (alpha < score)
				alpha = score;
			if (alpha >= beta)
				alpha = score;
			else while (index-- > 0)
				{
					if ((++g_totalNodes & 0x1fff) == 0)
						g_stop = GetStop();
					int cm = mu[index];
					MakeMove(cm);
					List<int> me = GenerateAllMoves(whiteTurn, true);
					int osScore = myMobility - adjMobility;
					g_depth = 0;
					g_pv = "";
					if (g_inCheck)
						osScore = -0xffff;
					else if (depth < depthL)
						osScore = -Quiesce(me, depth + 1, depthL, -beta, -alpha, -osScore);
					UnmakeMove(cm);
					if (g_stop) return -0xffff;
					if (alpha < osScore)
					{
						alpha = osScore;
						alphaDe = g_depth + 1;
						alphaPv = $"{FormatMove(cm)} {g_pv}";
					}
					if (alpha >= beta) break;
				}
			g_depth = alphaDe;
			g_pv = alphaPv;
			return alpha;
		}

		int GetScore(List<int> mu, int ply, int depthL, int alpha, int beta)
		{
			bool myInsufficient = adjInsufficient;
			int myMobility = adjMobility;
			int n = mu.Count;
			int myMoves = n;
			int alphaDe = 0;
			string alphaFm = "";
			string alphaPv = "";

			while (n-- > 0)
			{
				if ((++g_totalNodes & 0x1fff) == 0)
				{
					g_stop = ((depthL > 1) && GetStop()) || (CReader.ReadLine(false) == "stop");
				}
				int cm = mu[n];
				MakeMove(cm);
				List<int> me = GenerateAllMoves(whiteTurn, ply == depthL);
				g_depth = 0;
				g_pv = "";
				int osScore = myMobility - adjMobility;
				if (g_inCheck)
				{
					myMoves--;
					osScore = -0xffff;
				}
				else if ((g_move50 > 99) || IsRepetition() || ((adjInsufficient || osScore > 0) && myInsufficient))
					osScore = 0;
				else if (ply < depthL)
					osScore = -GetScore(me, ply + 1, depthL, -beta, -alpha);
				else
					osScore = -Quiesce(me, 1, depthL, -beta, -alpha, -osScore);
				UnmakeMove(cm);
				if (g_stop) return -0xffff;
				if (alpha < osScore)
				{
					alpha = osScore;
					alphaFm = FormatMove(cm);
					alphaPv = alphaFm + ' ' + g_pv;
					alphaDe = g_depth + 1;
					if (ply == 1)
					{
						if (osScore > 0xf000)
							g_scoreFm = $"mate {0xffff - osScore}";
						else if (osScore < -0xf000)
							g_scoreFm = $"mate {-0xfffe - osScore}";
						else
							g_scoreFm = $"cp {osScore}";
						bsIn = n;
						bsFm = alphaFm;
						bsPv = alphaPv;
						bsDepth = alphaDe;
						double t = stopwatch.Elapsed.TotalMilliseconds;
						double nps = 0;
						if (t > 0)
							nps = (g_totalNodes / t) * 1000;
						Console.WriteLine("info currmove " + bsFm + " currmovenumber " + n + " nodes " + g_totalNodes + " time " + Convert.ToInt64(t) + " nps " + Convert.ToInt64(nps) + " depth " + depthL + " seldepth " + alphaDe + " score " + g_scoreFm + " pv " + bsPv);
					}
				}
				if (alpha >= beta) break;
			}
			if (myMoves == 0)
			{
				GenerateAllMoves(whiteTurn ^ true, true);
				if (!g_inCheck)
				{
					alpha = 0;
				}
				else alpha = -0xffff + ply;
			}
			g_depth = alphaDe;
			g_pv = alphaPv;
			return alpha;
		}

		public void Start(int depth, int time, int nodes)
		{
			List<int> mu = GenerateAllMoves(whiteTurn, false);
			if (mu.Count == 0)
			{
				Console.WriteLine($"info string no moves");
				return;
			}
			bool myInsufficient = adjInsufficient;
			int myMobility = adjMobility;
			g_stop = false;
			g_totalNodes = 0;
			g_timeout = time;
			g_depthout = depth;
			g_nodeout = nodes;
			g_mainDepth = 1;
			do
			{
				adjInsufficient = myInsufficient;
				adjMobility = myMobility;
				GetScore(mu, 1, g_mainDepth, -0xffff, 0xffff);
				int m = mu[bsIn];
				mu.RemoveAt(bsIn);
				mu.Add(m);
				double t = stopwatch.Elapsed.TotalMilliseconds;
				double nps = 0;
				if (t > 0)
					nps = (g_totalNodes / t) * 1000;
				Console.WriteLine($"info depth {g_mainDepth} nodes {g_totalNodes} time {Convert.ToInt64(t)} nps {Convert.ToInt64(nps)} {mu.Count}");
				if (++g_mainDepth > 100)
					break;
			} while (!GetStop() && !g_stop && (mu.Count > 1));
			string[] ponder = bsPv.Split(' ');
			string pm = ponder.Length > 1 ? " ponder " + ponder[1] : "";
			Console.WriteLine("bestmove " + bsFm + pm);
		}

	}

	class CRapShort
	{
		static void Main(string[] args)
		{
			string version = "2020-04-04";
			CChess Chess = new CChess();
			CUci Uci = new CUci();

			while (true)
			{
				string msg = CReader.ReadLine(true);
				Uci.SetMsg(msg);
				switch (Uci.command)
				{
					case "uci":
						Console.WriteLine("id name RapShortCs " + version);
						Console.WriteLine("id author Thibor Raven");
						Console.WriteLine("id link https://github.com/Thibor/RapShortCs");
						Console.WriteLine("uciok");
						break;
					case "isready":
						Console.WriteLine("readyok");
						break;
					case "position":
						string fen = "";
						int lo = Uci.GetIndex("fen", 0);
						int hi = Uci.GetIndex("moves", Uci.tokens.Length);
						if (lo > 0)
						{
							if (lo > hi)
							{
								hi = Uci.tokens.Length;
							}
							for (int n = lo; n < hi; n++)
							{
								if (n > lo)
								{
									fen += ' ';
								}
								fen += Uci.tokens[n];
							}
						}
						Chess.InitializeFromFen(fen);
						lo = Uci.GetIndex("moves", 0);
						hi = Uci.GetIndex("fen", Uci.tokens.Length);
						if (lo > 0)
						{
							if (lo > hi)
							{
								hi = Uci.tokens.Length;
							}
							for (int n = lo; n < hi; n++)
							{
								string m = Uci.tokens[n];
								Chess.MakeMove(Chess.GetMoveFromString(m));
								if (Chess.g_move50 == 0)
									Chess.undoIndex = 0;
							}
						}
						break;
					case "go":
						Chess.stopwatch.Restart();
						int time = Uci.GetInt("movetime", 0);
						int depth = Uci.GetInt("depth", 0);
						int node = Uci.GetInt("nodes", 0);
						if ((time == 0) && (depth == 0) && (node == 0))
						{
							time = Chess.whiteTurn ? Uci.GetInt("wtime", 0) : Uci.GetInt("btime", 0);
							double mg = Uci.GetInt("movestogo", 32);
							time = Convert.ToInt32(time / mg);
							if (time < 1)
								time = 1;
						}
						if (time > 0)
						{
							time -= 0x20;
							if (time < 1)
							{
								time = 0;
								depth = 1;
							}
						}
						Chess.Start(depth, time, node);
						break;
					case "quit":
						return;
				}

			}
		}
	}
}
