require "fileutils"
require "benchmark"

test_cases = [
  { width:  1, depth:  1 },
  { width:  5, depth:  1 },
  { width:  10, depth:  1 },
  # { width: 20, depth:  1 },
  # { width:  1, depth: 20 },
  # { width:  5, depth:  5 },
]

`docker-compose run --rm whayrf 'make'`

Benchmark.bm do |x|
  test_cases.each do |test_case|
    test_name = "load_width_#{test_case[:width]}_depth_#{test_case[:depth]}"
    file_name = "../test-sources/#{test_name}.whayrf"
    `ruby generate_load_test.rb #{test_case[:width]} #{test_case[:depth]} > #{file_name}`
    x.report("Width: #{test_case[:width]}, Depth: #{test_case[:depth]}") do
      `docker-compose run --rm whayrf 'make test'`
    end
    FileUtils.rm file_name
  end
end
