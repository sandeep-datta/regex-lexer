#![doc(html_root_url = "https://docs.rs/regex-lexer/0.1.0/regex-lexer")]
//! A regex-based lexer (tokenizer).
//!
//! ```
//! use regex_lexer_lalrpop::LexerBuilder;
//!
//! #[derive(Debug, PartialEq, Eq)]
//! enum Token {
//!     Num(u32),
//!     Add,
//!     Sub,
//!     Mul,
//!     Div,
//!     Open,
//!     Close,
//! }
//!
//! let lexer = LexerBuilder::new()
//!     .token(r"[0-9]+", |_, tok, _| Some(Token::Num(tok.parse().unwrap())))
//!     .token(r"\+", |_, _, _| Some(Token::Add))
//!     .token(r"-", |_, _, _| Some(Token::Sub))
//!     .token(r"\*", |_, _, _| Some(Token::Mul))
//!     .token(r"/", |_, _, _| Some(Token::Div))
//!     .token(r"\(", |_, _, _| Some(Token::Open))
//!     .token(r"\)", |_, _, _| Some(Token::Close))
//!     .token(r"\s+", |_, _, _| None) // skip whitespace
//!     .build()?;
//!
//! let source = "(1 + 2) * 3";
//! assert_eq!(
//!     lexer.tokens(source).collect::<Vec<_>>(),
//!     vec![
//!         Ok(Token::Open), Ok(Token::Num(1)), Ok(Token::Add), Ok(Token::Num(2)), Ok(Token::Close),
//!         Ok(Token::Mul), Ok(Token::Num(3))
//!     ],
//! );
//! # Ok::<(), regex::Error>(())
//! ```

use std::fmt;
use regex::{Regex, RegexSet};

/// Location in text file being lexed.
#[derive(Clone, Copy, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct Location {
    line: u32,
    column: u32,
}

impl Location {
    fn new(line: u32, column: u32) -> Self {
        Location { line, column }
    }
}

impl fmt::Debug for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.line, self.column)
    }
}

/// Builder struct for [Lexer](struct.Lexer.html).
pub struct LexerBuilder<'r, 't, T: 't> {
    regexes: Vec<&'r str>,
    fns: Vec<Box<dyn Fn(Location, &'t str, Location) -> Option<T>>>,
}

impl<'r, 't, T: 't> std::fmt::Debug for LexerBuilder<'r, 't, T> {
    /// Shows the matched regexes
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("LexerBuilder")
            .field("regexes", &self.regexes)
            .finish() // todo: finish_non_exhaustive
    }
}

impl<'r, 't, T: 't> Default for LexerBuilder<'r, 't, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'r, 't, T: 't> LexerBuilder<'r, 't, T> {
    /// Create a new [LexerBuilder](struct.LexerBuilder.html).
    pub fn new() -> Self {
        LexerBuilder {
            regexes: Vec::new(),
            fns: Vec::new(),
        }
    }

    /// Add a new token that matches the regular expression `re`.
    /// This uses the same syntax as the [regex](http://docs.rs/regex/1/regex) crate.
    ///
    /// If `re` gives the longest match, then `f` is called on the matched string.
    /// * If `f` returns `Some(tok)`, emit the token `tok`.
    /// * Otherwise, skip this token and emit nothing.
    /// ```
    /// #[derive(Debug, PartialEq, Eq)]
    /// enum Token {
    ///     Num(usize),
    ///     // ...
    /// }
    ///
    /// let lexer = regex_lexer_lalrpop::LexerBuilder::new()
    ///     .token(r"[0-9]*", |_, num, _| Some(Token::Num(num.parse().unwrap())))
    ///     .token(r"\s+", |_, _, _| None) // skip whitespace
    ///     // ...
    ///     .build()?;
    ///
    /// assert_eq!(
    ///     lexer.tokens("1 2 3").collect::<Vec<_>>(),
    ///     vec![Ok(Token::Num(1)), Ok(Token::Num(2)), Ok(Token::Num(3))],
    /// );
    /// # Ok::<(), regex::Error>(())
    /// ```
    ///
    /// If multiple regexes all have the same longest match, then whichever is defined last
    /// is given priority.
    /// ```
    /// #[derive(Debug, PartialEq, Eq)]
    /// enum Token<'t> {
    ///     Ident(&'t str),
    ///     Then,
    ///     // ...
    /// }
    ///
    /// let lexer = regex_lexer_lalrpop::LexerBuilder::new()
    ///     .token(r"[a-zA-Z_][a-zA-Z0-9_]*", |_, id, _| Some(Token::Ident(id)))
    ///     .token(r"then", |_, _, _| Some(Token::Then))
    ///     // ...
    ///     .build()?;
    ///
    /// assert_eq!(lexer.tokens("then").next(), Some(Ok(Token::Then)));
    /// assert_eq!(lexer.tokens("then_perish").next(), Some(Ok(Token::Ident("then_perish"))));
    /// # Ok::<(), regex::Error>(())
    /// ```
    pub fn token<F>(mut self, re: &'r str, f: F) -> Self
    where
        F: Fn(Location, &'t str, Location) -> Option<T> + 'static,
    {
        self.regexes.push(re);
        self.fns.push(Box::new(f));
        self
    }

    /// Construct a [Lexer](struct.Lexer.html) which matches these tokens.
    ///
    /// ## Errors
    ///
    /// If a regex cannot be compiled, a [regex::Error](https://docs.rs/regex/1/regex/enum.Error.html) is returned.
    pub fn build(self) -> Result<Lexer<'t, T>, regex::Error> {
        let regexes = self.regexes.into_iter().map(|r| format!("^{}", r));
        let regex_set = RegexSet::new(regexes)?;
        let mut regexes = Vec::new();
        for pattern in regex_set.patterns() {
            regexes.push(Regex::new(pattern)?);
        }

        Ok(Lexer {
            fns: self.fns,
            regexes,
            regex_set,
        })
    }
}

/// A regex-based lexer.
///
/// ```
/// #[derive(Debug, PartialEq, Eq)]
/// enum Token<'t> {
///     Ident(&'t str),
///     // ...
/// }
///
/// let lexer = regex_lexer_lalrpop::LexerBuilder::new()
///     .token(r"\p{XID_Start}\p{XID_Continue}*", |_, id, _| Some(Token::Ident(id)))
///     .token(r"\s+", |_, _, _| None) // skip whitespace
///     // ...
///     .build()?;
///
/// let tokens = lexer.tokens("these are some identifiers");
///
/// # assert_eq!(
/// #    tokens.collect::<Vec<_>>(),
/// #    vec![Ok(Token::Ident("these")), Ok(Token::Ident("are")), Ok(Token::Ident("some")), Ok(Token::Ident("identifiers"))],
/// # );
/// # Ok::<(), regex::Error>(())
/// ```
pub struct Lexer<'t, T: 't> {
    fns: Vec<Box<dyn Fn(Location, &'t str, Location) -> Option<T>>>,
    regexes: Vec<Regex>,
    regex_set: RegexSet,
}

impl<'t, T: 't> Lexer<'t, T> {
    /// Create a [LexerBuilder](struct.LexerBuilder.html). This is the same as [LexerBuilder::new](struct.LexerBuilder.html#method.new).
    pub fn builder<'r>() -> LexerBuilder<'r, 't, T> {
        LexerBuilder::new()
    }

    /// Return an iterator over all matched tokens.
    pub fn tokens<'l>(&'l self, source: &'t str) -> Tokens<'l, 't, T> {
        Tokens {
            lexer: self,
            source,
            position: 0,
        }
    }
}

impl<'t, T: 't> std::fmt::Debug for Lexer<'t, T> {
    /// Shows the original regular expressions
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("Lexer")
            .field("regexes", &self.regexes)
            .finish() // todo: finish_non_exhaustive
    }
}

/// The type returned by [Lexer::tokens](struct.Lexer.html#method.tokens).
#[derive(Debug)]
pub struct Tokens<'l, 't, T: 't> {
    lexer: &'l Lexer<'t, T>,
    source: &'t str,
    position: usize,
}

fn get_line_column<'input>(input: &'input str, offset: usize) -> Location {
    let (before, _after) = input.split_at(offset);
    let line = before.chars().filter(|&c| c == '\n').count() + 1;
    let column = before.chars().rev().take_while(|&c| c != '\n').count() + 1;
    Location::new(line as u32, column as u32)
}

impl<'l, 't, T: 't> Iterator for Tokens<'l, 't, T> {
    type Item = Result<T, usize>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.position == self.source.len() {
                return None;
            }

            let string = &self.source[self.position..];
            let match_set = self.lexer.regex_set.matches(string);
            let matches = match_set
                .into_iter()
                .map(|i: usize| {
                    let m = self.lexer.regexes[i].find(string).unwrap();
                    assert!(m.start() == 0);
                    (m.end(), i)
                })
                .max_by_key(|(len, _)| *len);

            let matches = match matches {
                Some(matches) => matches,
                None => return Some(Err(self.position)),
            };

            let (len, i) = matches;

            let tok_str = &self.source[self.position..self.position + len];
            let start = self.position;
            self.position += len;
            let func = &self.lexer.fns[i];
            match func(get_line_column(self.source, start), 
                        tok_str, 
                        get_line_column(self.source, self.position))
            {
                Some(tok) => return Some(Ok(tok)),
                None => {}
            }
        }
    }
}
