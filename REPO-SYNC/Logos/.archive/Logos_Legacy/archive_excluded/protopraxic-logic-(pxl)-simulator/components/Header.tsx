
import React from 'react';

type Tab = 'simulator' | 'chat' | 'live';

interface HeaderProps {
  activeTab: Tab;
  setActiveTab: (tab: Tab) => void;
  agentIdentity: string | null;
}

const NavButton: React.FC<{
  label: string;
  isActive: boolean;
  onClick: () => void;
  disabled?: boolean;
  title?: string;
}> = ({ label, isActive, onClick, disabled = false, title = '' }) => {
  return (
    <button
      onClick={onClick}
      disabled={disabled}
      title={title}
      className={`px-4 py-2 rounded-md text-sm font-semibold transition-colors duration-200 focus:outline-none focus-visible:ring-2 focus-visible:ring-cyan-400 focus-visible:ring-offset-2 focus-visible:ring-offset-slate-900 ${
        isActive
          ? 'bg-cyan-500 text-white'
          : 'text-slate-300 hover:bg-slate-700/50'
      } ${
        disabled
          ? 'opacity-50 cursor-not-allowed'
          : ''
      }`}
    >
      {label}
    </button>
  );
};

const Header: React.FC<HeaderProps> = ({ activeTab, setActiveTab, agentIdentity }) => {
  const isLiveDisabled = !agentIdentity;

  return (
    <header className="sticky top-0 z-10 bg-slate-900/70 backdrop-blur-md">
      <div className="text-center py-4 px-4 border-b border-slate-700/50">
        <h1 className="text-2xl md:text-3xl font-bold text-transparent bg-clip-text bg-gradient-to-r from-cyan-400 to-purple-500">
          Protopraxic Logic (PXL) Core
        </h1>
        <p className="mt-1 text-slate-400 max-w-2xl mx-auto text-sm">
          An Interactive Simulator and AI Interface
        </p>
      </div>
      <nav className="border-b border-slate-700/50">
        <div className="container mx-auto px-4 md:px-8 py-2 flex justify-center items-center space-x-2 md:space-x-4">
          <NavButton
            label="PXL Simulator"
            isActive={activeTab === 'simulator'}
            onClick={() => setActiveTab('simulator')}
          />
          <NavButton
            label="Chat with Gemini"
            isActive={activeTab === 'chat'}
            onClick={() => setActiveTab('chat')}
          />
          <NavButton
            label="Live Conversation"
            isActive={activeTab === 'live'}
            onClick={() => !isLiveDisabled && setActiveTab('live')}
            disabled={isLiveDisabled}
            title={isLiveDisabled ? 'Complete the Agent Boot Sequence in the PXL Simulator first.' : 'Engage in a live conversation'}
          />
        </div>
      </nav>
    </header>
  );
};

export default Header;
