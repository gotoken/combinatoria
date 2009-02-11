require "rational"

module Combinatoria
  Id = "$kNotwork: combinatoria.rb,v 1.16 2003/04/20 20:09:56 gotoken Exp $"
  REVISION = Id[/\d+(\.\d+)+/]

  module Stream # ruby-list:13696
    def next
      callcc{|@cc|
        @cont.call if @cont
        @iter.call {|obj|
          callcc{|@cont| @cc.call(obj) }
        }
        @cc.call(nil)
      }
    end

    def rewind()
      @cont = @cc = nil
    end
  end

  class Combination
    include Enumerable
    include Stream

    def initialize(seq,k)
      @seq, @k = seq, k
      @size = Combinatoria::C(seq.size, @k)
      @iter, @cc, @cont = method(:each), nil, nil
    end

    attr_reader :size

    def each()
      # A tricky efficient algorithm which is developed by M. Beeler,
      # R. W. Gosper and R. Schroeppel (Samuel P. Harbison and 
      # Guy L. Steele Jr. "C: A Reference Manual.", Prentice-Hall, 
      # second edition, p176 (1987))

      n = @seq.size
      if n.zero? or @k.zero?
        yield(@seq.class.new())
        return
      else
        x = (1<<@k)-1
        comb = @seq.class.new
        (0..n-1).each{|i| comb << @seq[i] unless x[i].zero?}
        while (x & ~((1<<n)-1)).zero?
          yield(comb)
          smallest = x & -x
          ripple = x + smallest
          new_smallest = ripple & -ripple
          ones = ((new_smallest / smallest) >> 1) - 1
          x = ripple | ones
          comb = @seq.class.new
          (0..n-1).each{|i| comb << @seq[i] unless x[i].zero?}
        end
      end
    end
  end

  class Permutation
    include Enumerable
    include Stream

    def initialize(seq, k = nil)
      @seq, @k = seq, (k||seq.size)
      @size = Combinatoria::P(seq.size, @k)
      @iter, @cc, @cont = method(:each), nil, nil
    end

    def each(&block)
      if @k.zero?
        yield(@seq.class.new())
      elsif @k == @seq.size
        permutate(@seq,0,&block)
      else
        for comb in Combinatoria::Combination.new(@seq,@k)
          permutate(comb,0,&block)
        end
      end
    end

    private
    def permutate(a,k,&block)
      n = a.size-1
      if n == k
        yield(a)
      else
        for i in k..n
          b = a.dup
          b[k],b[i] = b[i],b[k]
          permutate(b,k+1,&block)
        end
      end
    end
  end

  class Subset
    include Enumerable
    include Stream

    def initialize(seq, k)
      @seq, @k = seq, (k || seq.size)
      @size = 2**seq.size
      @comb = Combinatoria::Combination.new(@seq,@i)
      @iter, @cc, @cont = method(:each), nil, nil
    end

    attr_reader :size

    def each()
      for i in 0..@k
        Combinatoria::Combination.new(@seq,i).each{|c| yield(c)}
      end
    end
  end

  module Iterator
    def combination(k)
      Combinatoria::Combination.new(self,k)
    end

    def each_combination(k, &block)
      Combinatoria::Combination.new(self,k).each(&block)
    end

    def combinations(k)
      Combinatoria::Combination.new(self,k).inject([]){|i,j| i<<j}
    end

    def permutation(k = size)
      Combinatoria::Permutation.new(self,k)
    end

    def each_permutation(k = size, &block)
      Combinatoria::Permutation.new(self,k).each(&block)
    end

    def permutations(k = size)
      Combinatoria::Permutation.new(self,k).inject([]){|i,j| i<<j}
    end

    def subset(k = size)
      Combinatoria::Subset.new(self,k)
    end

    def each_subset(k = size, &block)
      Combinatoria::Subset.new(self,k).each(&block)
    end

    def subsets(k = size)
      Combinatoria::Subset.new(self,k).inject([]){|i,j| i<<j}
    end
  end

  module_function

  def sum(range, zero=0)
    if block_given?
      range.inject(zero){|s,x| s+yield(x)}
    else
      range.inject(zero){|s,x| x}
    end
  end

  def product(range, one=1)
    if block_given?
      range.inject(one){|s,x| s*yield(x)}
    else
      range.inject(one){|s,x| s*x}
    end
  end

  def C(n,k)
    r = k < n/2 ? k : n-k
    (0..n) === k ? (1..k).inject(1){|i,j| i*(n-j+1)/j} : 0
  end

  def P(n,k)
    (0..n) === k ? (1..k).inject(1){|i,j| i*(n-j+1)} : 0
  end

  def H(n,k)
    Combinatoria::C(n+k-1,k)
  end

  Bernoulli = {0=>Rational(1,1)}

  def Bernoulli(k)
    Combinatoria::Bernoulli[k] ||= 
      -(0..k-1).inject(0){|s,i|s+C(k+1,k+1-i)*Bernoulli(i)}/C(k+1,1)
  end

  Stirling1 = {}

  def Stirling1(n,m)
    Combinatoria::Stirling1[[n,m]] ||=
      if n < m or n < 1 or m < 1
        0
      elsif n == m
        1
      else
        Stirling1(n-1,m-1) - (n-1)*Stirling1(n-1,m)
      end
  end

  Stirling2 = {}

  def Stirling2(n,m)
    Combinatoria::Stirling2[[n,m]] ||=
      if n < m or n < 1 or m < 1
        0
      elsif m == 1 or m == n
        1
      else
        Stirling2(n-1,m-1) + m*Stirling2(n-1,m)
      end
  end

  Partition = {}

  def Partition(n, m = nil)
    if m
      Combinatoria::Partition[[n,m]] ||=
        if n < m or n < 1 or m < 1
          0
        elsif m == 1 or m == n
          1
        else
          Partition(n-m,m) + Partition(n-1,m-1)
        end
    else
      Combinatoria::Partition[n] ||= (1..n).inject(0){|s,i| s+Partition(n,i)}
    end
  end

  def Bell(n)
    Combinatoria::Partition(n)
  end
end

class Array
  include Combinatoria::Iterator
end

class String
  include Combinatoria::Iterator
end

module Enumerable
  def combination(k)
    Combinatoria::Combination.new(to_a,k)
  end

  def each_combination(k, &block)
    Combinatoria::Combination.new(to_a,k).each(&block)
  end

  def combinations(k)
    Combinatoria::Combination.new(to_a,k).inject([]){|i,j| i<<j}
  end

  def permutation(k = size)
    Combinatoria::Permutation.new(to_a,k)
  end

  def each_permutation(k = size, &block)
    Combinatoria::Permutation.new(to_a,k).each(&block)
  end

  def permutations(k = size)
    Combinatoria::Permutation.new(to_a,k).inject([]){|i,j| i<<j}
  end

  def subset(k = size)
    Combinatoria::Subset.new(to_a,k)
  end

  def each_subset(k = size, &block)
    Combinatoria::Subset.new(to_a,k).each(&block)
  end

  def subsets(k = size)
    Combinatoria::Subset.new(to_a,k).inject([]){|i,j| i<<j}
  end
end
