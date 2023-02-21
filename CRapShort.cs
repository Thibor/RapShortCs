using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading;

namespace RapShortCs
{
	struct CUndo
	{
		public int captured;
		public int passing;
		public int castle;
		public int move50;
		public int lastCastle;
		public ulong hash;
	}

	class CUci
	{
		public string command;
		public string[] tokens;

		public int GetIndex(string key, int def)
		{
			for (int n = 0; n < tokens.Length; n++)
				if (tokens[n] == key)
					return n;
			return def;
		}

		public int GetInt(string key, int def)
		{
			for (int n = 0; n < tokens.Length - 1; n++)
				if (tokens[n] == key)
					return Int32.Parse(tokens[n + 1]);
			return def;
		}

		public string GetValue(string start)
		{
			int istart = GetIndex(start, tokens.Length);
			return GetValue(istart + 1);
		}

		public string GetValue(string start, string end)
		{
			int istart = GetIndex(start, tokens.Length);
			int iend = GetIndex(end, tokens.Length);
			return GetValue(istart + 1, iend - 1);
		}

		public string GetValue(int start, int end = 0)
		{
			string result = string.Empty;
			if (start < 0)
				start = 0;
			if ((end < start) || (end >= tokens.Length))
				end = tokens.Length - 1;
			for (int n = start; n <= end; n++)
				result += $" {tokens[n]}";
			return result.Trim();
		}

		public void SetMsg(string msg)
		{
			if (String.IsNullOrEmpty(msg))
			{
				tokens = new string[0];
				command = string.Empty;
			}
			else
			{
				tokens = msg.Trim().Split(' ');
				command = tokens[0];
			}
		}
	}

	struct D2
	{
		public int x;
		public int y;

		public D2(int sx, int sy)
		{
			x = sx;
			y = sy;
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
		public const int moveflagCastleKing = 0x04 << 16;
		public const int moveflagCastleQueen = 0x08 << 16;
		const int moveflagPromoteQueen = pieceQueen << 20;
		const int moveflagPromoteRook = pieceRook << 20;
		const int moveflagPromoteBishop = pieceBishop << 20;
		const int moveflagPromoteKnight = pieceKnight << 20;
		const int maskCastle = moveflagCastleKing | moveflagCastleQueen;
		const int maskColor = colorBlack | colorWhite;
		const int maskPromotion = moveflagPromoteQueen | moveflagPromoteRook | moveflagPromoteBishop | moveflagPromoteKnight;
		const int maskPassPromotion = maskPromotion | moveflagPassing;
		const int maskRank = 7;
		int usColor = 0;
		int enColor = 0;
		int inTime = 0;
		int inDepth = 0;
		int inNodes = 0;
		int castleRights = 0xf;
		ulong hash = 0;
		int passing = 0;
		public int move50 = 0;
		int halfMove = 0;
		int totalNodes = 0;
		bool inCheck = false;
		int g_timeout = 0;
		int g_depthout = 0;
		int g_nodeout = 0;
		int mainDepth = 1;
		bool g_stop = false;
		int lastCastle = 0;
		public int undoIndex = 0;
		readonly int[] board = new int[64];
		readonly ulong[,] hashBoard = new ulong[64, 16];
		readonly int[] boardCheck = new int[64];
		readonly int[] boardCastle = new int[64];
		public bool whiteTurn = true;
		string bsFm = String.Empty;
		string bsPv = String.Empty;
		readonly int[] bonMaterial = new int[7] { 0, 100, 340, 350, 525, 800, 0xffff };
		readonly D2[] arrDirKinght = { new D2(-2, -1), new D2(-2, 1), new D2(2, -1), new D2(2, 1), new D2(-1, -2), new D2(-1, 2), new D2(1, -2), new D2(1, 2) };
		readonly D2[] arrDirBishop = { new D2(-1, -1), new D2(-1, 1), new D2(1, -1), new D2(1, 1) };
		readonly D2[] arrDirRook = { new D2(-1, 0), new D2(1, 0), new D2(0, -1), new D2(0, 1) };
		readonly D2[] arrDirQueen = { new D2(-1, -1), new D2(-1, 1), new D2(1, -1), new D2(1, 1), new D2(-1, 0), new D2(1, 0), new D2(0, -1), new D2(0, 1) };
		public static Random random = new Random();
		readonly CUndo[] undoStack = new CUndo[0xfff];
		Thread startThread;
		public Stopwatch stopwatch = Stopwatch.StartNew();
		public CSynStop synStop = new CSynStop();

		public CChess()
		{
			hash = RAND_32();
			for (int n = 0; n < 64; n++)
			{
				boardCastle[n] = 15;
				boardCheck[n] = 0;
				board[n] = 0;
				for (int p = 0; p < 16; p++)
					hashBoard[n, p] = RAND_32();
			}
			boardCastle[0] = 7;
			boardCastle[4] = 3;
			boardCastle[7] = 11;
			boardCastle[56] = 13;
			boardCastle[60] = 12;
			boardCastle[63] = 14;
			boardCheck[3] = colorBlack | moveflagCastleQueen;
			boardCheck[4] = colorBlack | maskCastle;
			boardCheck[5] = colorBlack | moveflagCastleKing;
			boardCheck[59] = colorWhite | moveflagCastleQueen;
			boardCheck[60] = colorWhite | maskCastle;
			boardCheck[61] = colorWhite | moveflagCastleKing;
			SetFen();
		}

		ulong RAND_32()
		{
			return ((ulong)random.Next() << 32) | ((ulong)random.Next() << 0);
		}

		bool GetBoard(int x, int y, out int v)
		{
			v = 0;
			if ((x < 0) || (y < 0) || (x > 7) || (y > 7))
				return false;
			v = board[y * 8 + x];
			return true;
		}

		string EmoToUmo(int move)
		{
			string result = SquToStr(move & 0xFF) + SquToStr((move >> 8) & 0xFF);
			int promotion = move & maskPromotion;
			if (promotion > 0)
			{
				if (promotion == moveflagPromoteQueen) result += 'q';
				else if (promotion == moveflagPromoteRook) result += 'r';
				else if (promotion == moveflagPromoteBishop) result += 'b';
				else result += 'n';
			}
			return result;
		}

		public int UmoToEmo(string umo)
		{
			List<int> moves = GenerateAllMoves(whiteTurn, out _, out _);
			foreach (int m in moves)
				if (EmoToUmo(m) == umo)
					return m;
			return 0;
		}

		string SquToStr(int square)
		{
			int x = (square & 7);
			int y = (square >> 3);
			string xs = "abcdefgh";
			string ys = "87654321";
			return $"{xs[x]}{ys[y]}";
		}

		int StrToSqu(string s)
		{
			string xs = "abcdefgh";
			string ys = "87654321";
			int x = xs.IndexOf(s[0]);
			int y = ys.IndexOf(s[1]);
			return (y << 3) | x;
		}

		bool IsRepetition()
		{
			for (int n = undoIndex - 4; n >= undoIndex - move50; n -= 2)
				if (undoStack[n].hash == hash)
					return true;
			return false;
		}

		public void MakeMoves(string moves)
		{
			string[] am = moves.Split(new[] { ' ' }, StringSplitOptions.RemoveEmptyEntries);
			foreach (string m in am)
			{
				int emo = UmoToEmo(m);
				if (emo > 0)
					MakeMove(emo);
			}
		}

		void GeneratePawnAttack(List<int> moves, int fr, int to)
		{
			if (to == passing)
				GenerateMove(moves, fr, to, moveflagPassing, true);
			else if ((board[to] & colorEmpty) > 0)
				GenerateMove(moves, fr, to, 0, false);
			else if ((board[to] & enColor) > 0)
				GeneratePawnMoves(moves, fr, to, 0, true);
		}

		void GeneratePawnMoves(List<int> moves, int fr, int to, int flag, bool add)
		{
			int y = to >> 3;
			if ((y == 0) || (y == 7))
			{
				GenerateMove(moves, fr, to, moveflagPromoteQueen, true);
				GenerateMove(moves, fr, to, moveflagPromoteRook, true);
				GenerateMove(moves, fr, to, moveflagPromoteBishop, true);
				GenerateMove(moves, fr, to, moveflagPromoteKnight, true);
			}
			else
				GenerateMove(moves, fr, to, flag, add);
		}

		void GenerateUniMoves(List<int> moves, int fx, int fy, D2[] dir, int count, ref int score)
		{
			for (int n = 0; n < dir.Length; n++)
			{
				int fr = fy * 8 + fx;
				int dx = fx;
				int dy = fy;
				int c = count;
				while (c-- > 0)
				{
					D2 d = dir[n];
					dx += d.x;
					dy += d.y;
					if (!GetBoard(dx, dy, out int sq))
						break;
					int to = dy * 8 + dx;
					if ((sq & colorEmpty) > 0)
					{
						score++;
						GenerateMove(moves, fr, to, 0, true);
					}
					else if ((sq & enColor) > 0)
					{
						score += 2;
						GenerateMove(moves, fr, to, 0, true);
						break;
					}
					else
						break;
				}
			}
		}

		public void SetFen(string fen = "")
		{
			lastCastle = 0;
			synStop.SetStop(false);
			if (fen == "") fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
			string[] chunks = fen.Split();
			for (int n = 0; n < 64; n++)
				board[n] = colorEmpty;
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
					int piece = Char.IsUpper(c) ? colorWhite : colorBlack;
					int index = (row << 3) | col;
					switch (Char.ToLower(c))
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
					board[index] = piece;
					col++;
				}
			}
			whiteTurn = chunks[1] == "w";
			castleRights = 0;
			if (chunks[2].IndexOf('K') != -1)
				castleRights |= 1;
			if (chunks[2].IndexOf('Q') != -1)
				castleRights |= 2;
			if (chunks[2].IndexOf('k') != -1)
				castleRights |= 4;
			if (chunks[2].IndexOf('q') != -1)
				castleRights |= 8;
			passing = 0;
			if (chunks[3].IndexOf('-') == -1)
				passing = StrToSqu(chunks[3]);
			move50 = 0;
			halfMove = Int32.Parse(chunks[5]);
			if (halfMove > 0) halfMove--;
			halfMove *= 2;
			if (!whiteTurn) halfMove++;
			undoIndex = move50;
		}

		public void MakeMove(int move)
		{
			ref CUndo undo = ref undoStack[undoIndex++];
			undo.hash = hash;
			undo.passing = passing;
			undo.castle = castleRights;
			undo.move50 = move50;
			undo.lastCastle = lastCastle;
			int fr = move & 0xff;
			int to = (move >> 8) & 0xff;
			int piecefr = board[fr];
			int piece = piecefr & 0xf;
			int captured = board[to];
			lastCastle = (move & maskCastle) | (piecefr & maskColor);
			if ((move & moveflagCastleKing) > 0)
			{
				board[to - 1] = board[to + 1];
				board[to + 1] = colorEmpty;
			}
			else if ((move & moveflagCastleQueen) > 0)
			{
				board[to + 1] = board[to - 2];
				board[to - 2] = colorEmpty;
			}
			else if ((move & moveflagPassing) > 0)
			{
				int capi = whiteTurn ? to + 8 : to - 8;
				captured = board[capi];
				board[capi] = colorEmpty;
			}
			undo.captured = captured;
			hash ^= hashBoard[fr, piece];
			passing = -1;
			if ((captured & 0xf) > 0)
				move50 = 0;
			else if ((piece & 7) == piecePawn)
			{
				if (to == (fr + 16))
					passing = fr + 8;
				if (to == (fr - 16))
					passing = fr - 8;
				move50 = 0;
			}
			else
				move50++;
			int newPiece = ((move & maskPromotion) > 0) ? (piecefr & maskColor) | ((move >> 20) & maskRank) : piecefr;
			board[fr] = colorEmpty;
			board[to] = newPiece;
			hash ^= hashBoard[to, newPiece & 0xf];
			castleRights &= boardCastle[fr] & boardCastle[to];
			halfMove++;
			whiteTurn ^= true;
		}

		public void UnmakeMove(int move)
		{
			int fr = move & 0xFF;
			int to = (move >> 8) & 0xFF;
			int capi = to;
			CUndo undo = undoStack[--undoIndex];
			passing = undo.passing;
			castleRights = undo.castle;
			move50 = undo.move50;
			lastCastle = undo.lastCastle;
			hash = undo.hash;
			int captured = undo.captured;
			if ((move & moveflagCastleKing) > 0)
			{
				board[to + 1] = board[to - 1];
				board[to - 1] = colorEmpty;
			}
			else if ((move & moveflagCastleQueen) > 0)
			{
				board[to - 2] = board[to + 1];
				board[to + 1] = colorEmpty;
			}
			if ((move & maskPromotion) > 0)
			{
				int piece = (board[to] & (~0x7)) | piecePawn;
				board[fr] = piece;
			}
			else board[fr] = board[to];
			if ((move & moveflagPassing) > 0)
			{
				capi = whiteTurn ? to - 8 : to + 8;
				board[to] = colorEmpty;
			}
			board[capi] = captured;
			halfMove--;
			whiteTurn ^= true;
		}

		bool GetStop()
		{
			return ((g_timeout > 0) && (stopwatch.Elapsed.TotalMilliseconds > g_timeout)) || ((g_depthout > 0) && (mainDepth > g_depthout)) || ((g_nodeout > 0) && (totalNodes > g_nodeout));
		}

		List<int> GenerateAllMoves(bool wt, out int score, out bool insufficient)
		{
			score = 0;
			inCheck = false;
			usColor = wt ? colorWhite : colorBlack;
			enColor = wt ? colorBlack : colorWhite;
			int pieceP = 0;
			int pieceN = 0;
			int pieceB = 0;
			int pieceM = 0;
			int kpx = 0;
			int kpy = 0;
			List<int> moves = new List<int>(64);
			for (int x = 0; x < 8; x++)
			{
				for (int y = 0; y < 8; y++)
				{
					int fr = (y << 3) | x;
					int f = board[fr];
					if ((f & usColor) > 0) f &= 7;
					else continue;
					score += bonMaterial[f];
					switch (f)
					{
						case 1:
							pieceP++;
							int del = wt ? -1 : 1;
							int to = fr + del * 8;
							score += wt ? 1 << (7 - y) : 1 << y;
							if (((board[to] & colorEmpty) > 0))
							{
								GeneratePawnMoves(moves, fr, to, 0, true);
								int d = wt ? 6 : 1;
								if ((y == d) && (board[fr + del * 16] & colorEmpty) > 0)
									GeneratePawnMoves(moves, fr, fr + del * 16, 0, true);
							}
							if (GetBoard(x - 1, y + del, out _))
								GeneratePawnAttack(moves, fr, to - 1);
							if (GetBoard(x + 1, y + del, out _))
								GeneratePawnAttack(moves, fr, to + 1);
							break;
						case 2:
							pieceN++;
							GenerateUniMoves(moves, x, y, arrDirKinght, 1, ref score);
							break;
						case 3:
							pieceB++;
							GenerateUniMoves(moves, x, y, arrDirBishop, 7, ref score);
							break;
						case 4:
							pieceM++;
							GenerateUniMoves(moves, x, y, arrDirRook, 7, ref score);
							break;
						case 5:
							pieceM++;
							GenerateUniMoves(moves, x, y, arrDirQueen, 7, ref score);
							break;
						case 6:
							kpx = x;
							kpy = y;
							GenerateUniMoves(moves, x, y, arrDirQueen, 1, ref score);
							int cr = wt ? castleRights : castleRights >> 2;
							if ((cr & 1) > 0)
								if (((board[fr + 1] & colorEmpty) > 0) && ((board[fr + 2] & colorEmpty) > 0))
									GenerateMove(moves, fr, fr + 2, moveflagCastleKing, true);
							if ((cr & 2) > 0)
								if (((board[fr - 1] & colorEmpty) > 0) && ((board[fr - 2] & colorEmpty) > 0) && ((board[fr - 3] & colorEmpty) > 0))
									GenerateMove(moves, fr, fr - 2, moveflagCastleQueen, true);
							break;
					}
				}
			}
			if (pieceB > 1)
				score += 0x40;
			int dx = Math.Abs((kpx << 1) - 7) >> 1;
			int dy = Math.Abs((kpy << 1) - 7) >> 1;
			int phase = pieceP + pieceN + pieceB + pieceM;
			score += (phase - 8) * (dx + dy);
			insufficient = (pieceP + pieceM == 0) && (pieceN + (pieceB << 1) < 3);
			return moves;
		}

		void GenerateMove(List<int> moves, int fr, int to, int flag, bool add)
		{
			int rank = board[to] & 7;
			if (((board[to] & 7) == pieceKing) || (((boardCheck[to] & lastCastle) == lastCastle) && ((lastCastle & maskCastle) > 0)))
				inCheck = true;
			else if (add)
				if ((rank > 0) || ((flag & maskPassPromotion) > 0))
					moves.Add(fr | (to << 8) | flag);
				else
					moves.Insert(0, fr | (to << 8) | flag);
		}

		int Search(List<int> mu, int ply, int depth, int alpha, int beta, int usScore, bool usInsufficient, ref int alDe, ref string alPv, out int myMoves)
		{
			int neDe = 0;
			string nePv = "";
			int n = mu.Count;
			myMoves = n;
			while (n-- > 0)
			{
				int cm = mu[n];
				alDe = 0;
				alPv = string.Empty;
				if ((++totalNodes & 0x1fff) == 0)
					if (GetStop() || synStop.GetStop())
						g_stop = mainDepth > 0;
				MakeMove(cm);
				List<int> me = GenerateAllMoves(whiteTurn, out int enScore, out bool enInsufficient);
				int score = usScore - enScore;
				if (usInsufficient != enInsufficient)
					score += usInsufficient ? -400 : 400;
				if (inCheck)
				{
					myMoves--;
					score = -0xffff;
				}
				else if ((move50 > 99) || IsRepetition() || (usInsufficient && enInsufficient))
					score = 0;
				else if (depth > 1)
					score = -Search(me, ply + 1, depth - 1, -beta, -alpha, enScore, enInsufficient, ref alDe, ref alPv, out _);
				UnmakeMove(cm);
				if (g_stop) return -0xffff;
				if (score >= beta)
					return beta;
				if (score > alpha)
				{
					string alphaFm = EmoToUmo(cm);
					nePv = $"{alphaFm} {alPv}";
					neDe = alDe + 1;
					alpha = score;
					if (ply == 1)
					{
						string scFm = score > 0xf000 ? $"mate {(0xffff - score) >> 1}" : ((score < -0xf000) ? $"mate {(-0xfffe - score) >> 1}" : $"cp {score}");
						bsFm = alphaFm;
						bsPv = nePv;
						mu.RemoveAt(n);
						mu.Add(cm);
						double t = stopwatch.Elapsed.TotalMilliseconds;
						double nps = t > 0 ? (totalNodes / t) * 1000 : 0;
						Console.WriteLine($"info currmove {bsFm} currmovenumber {mu.Count - n} nodes {totalNodes} time {Convert.ToInt64(t)} nps {Convert.ToInt64(nps)} depth {mainDepth} seldepth {neDe} score {scFm} pv {nePv}");
					}
				}
			}
			alDe = neDe;
			alPv = nePv;
			if (myMoves == 0)
			{
				GenerateAllMoves(!whiteTurn, out _, out _);
				return inCheck ? -0xffff + ply : 0;
			}
			return alpha;
		}

		public void Start(int depth, int time, int nodes)
		{
			List<int> mu = GenerateAllMoves(whiteTurn, out int usScore, out bool usInsufficient);
			int myMoves;
			g_stop = false;
			totalNodes = 0;
			g_timeout = time;
			g_depthout = depth;
			g_nodeout = nodes;
			mainDepth = 1;
			do
			{
				int alDe = 0;
				string alPv = "";
				int score = Search(mu, 1, mainDepth, -0xffff, 0xffff, usScore, usInsufficient, ref alDe, ref alPv, out myMoves);
				double t = stopwatch.Elapsed.TotalMilliseconds;
				double nps = t > 0 ? (totalNodes / t) * 1000 : 0;
				Console.WriteLine($"info depth {mainDepth} nodes {totalNodes} time {Convert.ToInt64(t)} nps {Convert.ToInt64(nps)}");
				mainDepth++;
				if (mainDepth > 100)
					break;
				if ((score < -0xf000) || (score > 0xf000))
					break;
			} while (!GetStop() && !synStop.GetStop() && (myMoves > 1));
			string[] ponder = bsPv.Trim().Split();
			string pm = ponder.Length > 1 ? $" ponder {ponder[1]}" : string.Empty;
			Console.WriteLine("bestmove " + bsFm + pm);
		}

		public void Thread()
		{
			Start(inDepth, inTime, inNodes);
		}

		public void StartThread(int depth, int time, int nodes)
		{
			inDepth = depth;
			inTime = time;
			inNodes = nodes;
			startThread = new Thread(Thread);
			startThread.Start();
		}

	}

	class CSynStop
	{
		private bool value = true;
		private readonly object locker = new object();

		public bool GetStop()
		{
			lock (locker)
			{
				return value;
			}
		}

		public void SetStop(bool v)
		{
			lock (locker)
			{
				value = v;
			}
		}

	}

	class CRapShort
	{
		static void Main()
		{
			string version = "2023-02-21";
			CChess chess = new CChess();
			CUci uci = new CUci();

			while (true)
			{
				string msg = Console.ReadLine();
				uci.SetMsg(msg);
				switch (uci.command)
				{
					case "uci":
						Console.WriteLine($"id name RapShortCs {version}");
						Console.WriteLine("id author Thibor Raven");
						Console.WriteLine("id link https://github.com/Thibor/RapShortCs");
						Console.WriteLine("uciok");
						break;
					case "isready":
						Console.WriteLine("readyok");
						break;
					case "position":
						chess.SetFen(uci.GetValue("fen", "moves"));
						chess.MakeMoves(uci.GetValue("moves"));
						break;
					case "go":
						chess.stopwatch.Restart();
						int time = uci.GetInt("movetime", 0);
						int depth = uci.GetInt("depth", 0);
						int node = uci.GetInt("nodes", 0);
						int infinite = uci.GetIndex("infinite", 0);
						if ((time == 0) && (depth == 0) && (node == 0) && (infinite == 0))
						{
							double ct = chess.whiteTurn ? uci.GetInt("wtime", 0) : uci.GetInt("btime", 0);
							double inc = chess.whiteTurn ? uci.GetInt("winc", 0) : uci.GetInt("binc", 0);
							double mg = uci.GetInt("movestogo", 32);
							time = Convert.ToInt32((ct - 1000 + inc * mg) / mg);
							if (time < 1)
								time = 1;
						}
						chess.StartThread(depth, time, node);
						break;
					case "stop":
						chess.synStop.SetStop(true);
						break;
					case "quit":
						chess.synStop.SetStop(true);
						return;
				}

			}
		}
	}
}
