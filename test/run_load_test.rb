require "fileutils"
require "benchmark"

test_cases = [

  # Smoke test.

  { width: 1, depth: 1 },

  # Width deep.

  { width:  8, depth: 1 },
  { width:  9, depth: 1 },
  { width: 10, depth: 1 },
  { width: 11, depth: 1 },
  { width: 12, depth: 1 },
  { width: 13, depth: 1 },
  { width: 14, depth: 1 },
  { width: 15, depth: 1 },

  # Square.

  { width:  2, depth:  2 },

  # Takes a long while/never finishes.

  { width:  1, depth:  8 },
  { width:  5, depth:  5 },
]

`cd .. && make > /dev/null 2>&1`

label_length = 20
Benchmark.bm(label_length) do |x|
  test_cases.each do |test_case|
    test_name = "load_width_#{test_case[:width]}_depth_#{test_case[:depth]}"
    file_name = "../test-sources/#{test_name}.whayrf"
    `ruby generate_load_test.rb #{test_case[:width]} #{test_case[:depth]} > #{file_name}`
    x.report("Width: #{test_case[:width]}, Depth: #{test_case[:depth]}") do
      `cd .. && make test > /dev/null 2>&1`
    end
    FileUtils.rm file_name
  end
end
