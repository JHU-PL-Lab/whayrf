test_cases = [
  { width:  1, depth:  1 },
  { width: 20, depth:  1 },
  { width:  1, depth: 20 },
  { width:  5, depth:  5 },
]

test_cases.each do |test_case|
  `ruby generate_load_test.rb #{test_case[:width]} #{test_case[:depth]} > ../test-sources/load_width_#{test_case[:width]}_depth_#{test_case[:depth]}.whayrf`
end
