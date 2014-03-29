#include <iostream>
#include <string>
#include <boost/asio.hpp>
#include <boost/bind.hpp>
#include "server.hpp"

int main(int argc, char* argv[])
{
  try
  {
    // Check command line arguments.
    if (argc != 2)
    {
      std::cerr << "Usage: http_server <address>";
      return 1;
    }

    // Initialize the server.
    http::server::server s(argv[1], "8845", ".");

    // Run the server until stopped.
    s.run();
  }
  catch (std::exception& e)
  {
    std::cerr << "exception: " << e.what() << "\n";
  }

  return 0;
}
