"""desubstitute.py -- A basic cracker for substitution ciphers.

Usage:
  python desubstitute.py <word_count_file> <ciphertext>
  - or -
  python desubstitute.py <word_count_file> <rotation> <cleartext>

The word count file should be "word{tab}count", one per line, preferably sorted
in descending order by count.

If invoked with two arguments, the solver will attempt to crack the ciphertext.

If invoked with three arguments, the cleartext will be encrypted with a 
rotation cipher of the given distance, and then the solver will attempt to crack
the encrypted text.

Improvements:

Right now, the solver will guess the highest probability individual words, but
does not take into account multiple word probabilities. It would be good to add
word bigram probabilities. 

The solver does not do well with unknown words, or uncommon words in short
phrases. This could be helped by adding a language model based on letters as
well as the one based on words, such as single letter or pair letter frequency.

Also, it does not handle punctuation or numbers in the cleartext.
"""
import sys
import collections
import bisect
import random
import re
import csv
import string


def usage():
  print '''
Usage:
  python desubstitute.py <word_count_file> <ciphertext>
  - or -
  python desubstitute.py <word_count_file> <rotation> <cleartext>
  '''


# Global definition of the character to use a placeholder for unknowns. This 
# must not be present in the word counts, ciphertext, or cleartext.
blank_char = '*'


"""Cipher: Wraps a dictionary of character substitutions for encoding/decoding.

It supports partial maps and will replace unknown characters with blank_char
defined globally above.
"""
class Cipher(object):

  # Decipher is dict that maps cipher=>clear for each character, can be partial.
  def __init__(self, decipher={}):
    self.decipher = decipher 
    self.decipher[' '] = ' '  # Pass spaces through unchanged.
    self.encipher = dict((y,x) for x,y in self.decipher.iteritems())
    self.blank = blank_char

  def _replace(self, mapping, text):
    return ''.join(
        [(mapping[t] if t in mapping else self.blank) for t in text])

  def encode(self, cleartext):
    return self._replace(self.encipher, cleartext)
  
  def decode(self, ciphertext):
    return self._replace(self.decipher, ciphertext)

  def update(self, decipher):
    self.decipher.update(decipher)
    self.encipher = dict((y,x) for x,y in self.decipher.iteritems())

  def is_complete(self, text):
    return all(t in self.decipher for t in text)


"""tokenize: Parses a string into a list of word tokens.
"""
def tokenize(text):
  # TODO This should probably do something sensible with punctuation instead of
  # just dropping it.
  return [filter(lambda x: x in string.letters, word.lower()) 
      for word in text.split()]


"""Desubstitute: Class for performing a crack on a substitution cipher.
"""
class Desubstitute(object):
  word_count_exponent = .5  # Take the square root of word counts.

  def __init__(self, word_counts):
    # Prefer already sorted from the file, but sort it just in case. This is a
    # cheap operation if the list is already sorted.
    word_counts.sort(key=lambda x: x[1], reverse=True)
    # Bucket the list by word length for faster regexp matching.
    self.word_counts_by_length = collections.defaultdict(list)
    for x in word_counts:
      self.word_counts_by_length[len(x[0])].append(
          (x[0], (x[1]/float(word_counts[0][1]))**self.word_count_exponent))
    # Cache word scores for speed.
    self.word_score_cache = {}

  def score_unknown_word(self, word):
    # This is the old version.
    return 0
    # This works like Option 2 in _score_word(...)
    #return -1*self.word_counts_by_length[1][0][1]

  """_score_word: Score a single word, called from score_word(...) for caching.
  
  Currently returns the normalized count of the maximum possible fuzzy matched
  word based on the word counts passed in the constructor.
  """
  def _score_word(self, word):
    # There is probably a faster way to fuzzy match words than regexp matching
    # with a length index, but this was easy to write.
    curr_word_counts = self.word_counts_by_length[len(word)]
    # Regexp that looks for a whole word matching known cleartext letters
    # exactly and matching any letter for an unknown cleartext letter.
    matcher = re.compile('\\b'+word.replace(blank_char, '[a-z]')+'\\b')
    for c in curr_word_counts:
      if matcher.match(c[0]): return c[1]
    return self.score_unknown_word(word)

  """score_word: Score a single word using _score_word(...) and cache output.
  """
  def score_word(self, word):
    if word not in self.word_score_cache:
      self.word_score_cache[word] = self._score_word(word)
    return self.word_score_cache[word]

  """score_words: Score multiple words.

  This uses a combination of score_word(...) and a penalty for unknown words.
  Several options that were experimented with are included below in comments.
  """
  def score_words(self, words):
    # This would be improved by adding a scoring function for unknown words
    # that used letter ngrams to score unkown words and then scaling that score
    # up to the maximum score for a word of that length.
    word_scores = [self.score_word(x) for x in words]
    unmatched_words = [words[i] for i in xrange(len(words)) 
        if word_scores[i] == 0]
    num_unmatched = len(unmatched_words)
    # Various possible scoring algorithms tried below.
    #
    # Option 1: Two-part score, unknown words penalized in first term.
    # This works when all words are known, but failed to terminate in a 
    # reasonable amount of time on an input with an unknown word.
    #return (-1*num_unmatched, sum(word_scores))
    #
    # Option 2: Single score with maximum word score penalty for unknown word.
    # This one works just as well as Option 1 with known words, and finds a
    # close but still incorrect solution with an unknown word.
    return sum(word_scores) - num_unmatched*self.word_counts_by_length[1][0][1]
    #
    # Option 3: Single score with word score penalty based on word length.
    #
    # This one fails on both known and unknown word inputs, but is much faster
    # to find the same nearly-correct solution with an unknown word as Option 2.
    #return sum(word_scores) - sum(
    #    [self.word_counts_by_length[len(w)][0][1] for w in unmatched_words])
    #
    # Option 4: The same as Option 3 but with a fudge factor added.
    # With penalty_mult=10, this gets the correct answer for known words,
    # and gets quite close with unknown words, but still not quite correct.
    #penalty_mult = 10
    #return sum(word_scores) - sum(
    #    [self.word_counts_by_length[len(w)][0][1]*penalty_mult
    #      for w in unmatched_words])
    #
    # For using self.score_unknown_word, just pass those scores through.
    #return sum(word_scores)


  """choose_weakest_letter: Picks the next letter to try cracking.

  Current heuristic is just to choose the most common letter.
  """
  @staticmethod
  def choose_weakest_letter(tokens, cipher):
    # Choose the most common letter.
    # TODO Possibly combine with a heuristic for prioritizing "almost finished"
    # whole words.
    letter_counts = collections.defaultdict(int)
    for t in tokens:
      for c in t:
        letter_counts[c] += 1
    count = 0 
    letter = None
    for l,c in letter_counts.iteritems():
      if c > count and l not in cipher.decipher:
        letter = l
        count = c
    return letter

  """_scored_node: Return a node tuple from the given components.

  Node structure is a tuple (score, decipher, modification) where:
  - score is the score for all tokens based on the cipher
  - decipher is a dict mapping characters {cipher:clear}
  - modification is the last character changed (parameter passed is unchanged)
  """
  def _scored_node(self, tokens, cipher, modification=None):
    return (
        self.score_words([cipher.decode(x) for x in tokens]),
        dict(cipher.decipher),
        modification
        )

  """_create_child_nodes: Create new nodes for all possible next deciphers.

  The next letter to decipher is chosen using choose_weakest_letter(...) and
  then all possible choices are scored using score_words(...).
  """
  def _create_child_nodes(self, tokens, cipher):
    target_cipher_letter = self.choose_weakest_letter(tokens, cipher)
    assert(len(target_cipher_letter)==1)
    # Create and score an output node for each possible next decoding.
    candidate_chars = filter(lambda x: x not in cipher.decipher.values(),
        string.lowercase)
    output = []
    for candidate in candidate_chars:
      cipher.update({target_cipher_letter:candidate})
      output.append(self._scored_node(tokens, cipher, target_cipher_letter))
    return output

  """_solve: The top-level loop for the solver.
  """
  def _solve(self, tokens):
    # List invariant: in sorted order ascending, best node at the high index.
    nodes = [self._scored_node(tokens, Cipher())]
    cipher = None
    while nodes:
      # Get the current best candidate from the top of the queue.
      node = nodes.pop()
      cipher = Cipher(node[1])
      # Print progress
      curr_output = cipher.decode(' '.join(tokens))
      if node[2] is not None:
        latest_char = cipher.decode(node[2])
        curr_output = curr_output.replace(latest_char, latest_char.upper())
      curr_output += ' | %s' % str(node[0])  # Score.
      curr_output += ' [%d]' % len(nodes)  # Queue size.
      print curr_output
      # Check if we have fully cracked it and return if so.
      latest_decode = cipher.decode(' '.join(tokens))
      if not cipher.blank in latest_decode:
        return cipher
      # Replace top scoring node with all possible children.
      additions = self._create_child_nodes(tokens, cipher)
      # Check if we got any complete ciphers, return early if so.
      for a in additions:
        if len(a[1]) == 26:
          return a[1]
      # Otherwise, insert sorted into the queue.
      for a in additions:
        bisect.insort(nodes, a)
    return cipher

  """solve: Tokenizes input text and runs _solve(...).
  """
  def solve(self, text):
    return self._solve(tokenize(text))


"""rotation_cipher: Creates a Cipher based on a rotation around the alphabet.
"""
def rotation_cipher(rotate=None):
  if rotate is None:
    rotate = int(random.random()*26)
  cipher_map = dict(
      (string.letters[(i+rotate)%26],string.letters[i]) for i in xrange(26))
  cipher = Cipher(cipher_map)
  return cipher


"""load_word_counts_from_file: Read in the word count file into a list.
"""
def load_word_counts_from_file(filename):
  with open(filename) as fid:
    word_counts = [(x[0], int(x[1])) for x in csv.reader(fid, delimiter='\t')]
  return word_counts


if __name__ == '__main__':
  if len(sys.argv) not in [3,4]:
    usage()
    sys.exit(0)
  word_counts_file = sys.argv[1]
  word_counts = load_word_counts_from_file(word_counts_file)
  if len(sys.argv) == 4:
    test_cipher = rotation_cipher(int(sys.argv[2]))
    test_cleartext = sys.argv[3].strip()
    test_ciphertext = test_cipher.encode(test_cleartext)
  else:
    test_ciphertext = sys.argv[2].strip()
  print test_ciphertext
  solver = Desubstitute(word_counts)
  result = solver.solve(test_ciphertext)
  print result.decipher
  print result.decode(test_ciphertext)
